use std::{borrow::Cow, sync::Arc};

use dashmap::DashMap;

use crate::{Hashed, NodeStore, error::SmtError, lowlevel::RawNode};

/// A "snapshot" of a NodeStore, which can be written into storage without unreferenced nodes.
#[derive(Debug)]
pub struct GcSnapshot<'a, T: NodeStore> {
    inner: &'a T,
    mapping: Arc<DashMap<Hashed, RawNode<'a>>>,
}

impl<'a, T: NodeStore> Clone for GcSnapshot<'a, T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner,
            mapping: self.mapping.clone(),
        }
    }
}

impl<'a, T: NodeStore> GcSnapshot<'a, T> {
    pub fn new(inner: &'a T) -> Self {
        Self {
            inner,
            mapping: Default::default(),
        }
    }

    pub fn get_node(&self, hash: Hashed) -> Result<Option<RawNode<'a>>, SmtError> {
        if hash == [0; 32] {
            Ok(None)
        } else {
            if let Some(res) = self.mapping.get(&hash) {
                return Ok(Some(res.clone()));
            }
            if let Some(gotten) = self.inner.get(&hash)? {
                let view = match gotten {
                    Cow::Borrowed(gotten) => RawNode::try_from_slice(gotten)
                        .ok_or_else(|| SmtError::DbCorrupt(anyhow::anyhow!("corrupt node")))?,
                    Cow::Owned(gotten) => RawNode::try_from_slice(&gotten)
                        .ok_or_else(|| SmtError::DbCorrupt(anyhow::anyhow!("corrupt node")))?
                        .into_owned(),
                };
                Ok(Some(view))
            } else {
                Ok(None)
            }
        }
    }

    pub fn insert(&self, key: Hashed, value: RawNode<'a>) {
        if key != [0; 32] {
            self.mapping.insert(key, value);
        }
    }

    pub fn gc_commit(&self, root: Hashed) -> Result<(), SmtError> {
        // Look up the node without removing it yet.
        let val = if let Some(entry) = self.mapping.get(&root) {
            entry.clone() // take an owned copy we can work with
        } else {
            return Ok(()); // nothing buffered for this hash
        };

        match &val {
            RawNode::Single(_, _, _) => {
                self.inner.insert(&root, &val.to_bytes())?;
            }
            RawNode::Hexary(_, _, children) => {
                for child in children.iter() {
                    self.gc_commit(*child)?; // commit descendants
                }
                self.inner.insert(&root, &val.to_bytes())?;
            }
        }

        // Now that the node (and its subtree) is safely stored, purge it
        // from the in-memory mapping.
        self.mapping.remove(&root);
        Ok(())
    }
}
