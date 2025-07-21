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
    pub fn get_node(&self, hash: Hashed) -> Result<Option<RawNode<'a>>, SmtError> {
        if hash == [0; 32] {
            Ok(None)
        } else {
            if let Some(res) = self.mapping.get(&hash) {
                return Ok(Some(res.clone()));
            }
            if let Some(gotten) = self.inner.get(&hash) {
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
}
