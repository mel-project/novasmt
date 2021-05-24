use bytes::Bytes;
use parking_lot::RwLock;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::Hashed;

/// A trait that encapsulates a backend database to store on-disk SMT nodes.
pub trait BackendDB: Send + Sync + 'static {
    /// Adds a batch of key-value bindings to the backend. This must reach disk atomically.
    fn set_batch(&self, kvv: &[(Hashed, BackendNode)]);

    /// Reads a BackendNode from the backend.
    fn get(&self, key: Hashed) -> Option<BackendNode>;

    /// Deletes a root from the backend. This should also delete any nodes that as a result become unreachable. Backends have the choice of using reference counting or any other garbage-collection method they choose.
    fn delete_root(&self, key: Hashed);

    /// Queues a root to be deleted *on the next startup*. If this key is then set with set_batch, the backend MUST remove the root from the queue.
    fn delete_root_tomorrow(&self, key: Hashed);
}

/// A representation of a node in the backend database.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum BackendNode {
    /// Internal node, with two children
    Internal(Hashed, Hashed),
    /// Leaf node, with a key-value pair
    Leaf(Hashed, Bytes),
}

/// An in-memory backend DB, for testing and demos.
#[derive(Default)]
pub struct InMemoryBackend {
    inner: RwLock<HashMap<Hashed, (BackendNode, usize)>>,
}

impl BackendDB for InMemoryBackend {
    fn set_batch(&self, kvv: &[(Hashed, BackendNode)]) {
        let mut inner = self.inner.write();
        let mut increment = Vec::new();
        for (k, v) in kvv {
            if inner.insert(*k, (v.clone(), 0)).is_none() {
                if let BackendNode::Internal(left, right) = v {
                    increment.push(*left);
                    increment.push(*right);
                }
            }
        }
        // increment everything in increment
        for hash in increment {
            if hash != [0; 32] {
                inner.get_mut(&hash).unwrap().1 += 1;
            }
        }
    }

    fn get(&self, key: Hashed) -> Option<BackendNode> {
        self.inner.read().get(&key).map(|v| v.0.clone())
    }

    fn delete_root(&self, key: Hashed) {
        log::trace!("deleting root {:?}", key);
        let mut inner = self.inner.write();
        if !inner.contains_key(&key) {
            log::trace!("NOTHING deleted");
            return;
        }
        let mut to_delete = Vec::new();
        let mut dfs_stack: Vec<Hashed> = vec![key];
        while let Some(top) = dfs_stack.pop() {
            if top == [0; 32] {
                continue;
            }
            let (bnode, refcount) = inner
                .get_mut(&top)
                .map(|v| (v.0.clone(), &mut v.1))
                .unwrap();
            *refcount = refcount.saturating_sub(1);
            if *refcount == 0 {
                to_delete.push(top);
                if let BackendNode::Internal(left, right) = bnode {
                    dfs_stack.push(left);
                    dfs_stack.push(right);
                }
            }
        }
        log::trace!("deleting {} in total", to_delete.len());
        for hash in to_delete {
            inner.remove(&hash).unwrap();
        }
    }

    fn delete_root_tomorrow(&self, _key: Hashed) {
        // noop
    }
}
