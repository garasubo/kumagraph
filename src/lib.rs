use std::sync::{Arc, Mutex, Weak};
use std::clone::Clone;

#[derive(Debug, Clone)]
struct GraphInner<T> {
    nodes: Vec<(Option<Arc<Mutex<NodeInner<T>>>>, usize)>,
    next: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum GraphError {
    NodeDead,
    InvalidNode,
    LockFailure,
}


#[derive(Debug, Clone)]
pub struct Graph<T>(Arc<Mutex<GraphInner<T>>>);

impl<T> Graph<T> {
    pub fn new() -> Self {
        let inner = GraphInner { 
            nodes: Vec::new(),
            next: 0,
        };
        Self(Arc::new(Mutex::new(inner)))
    }

    pub fn new_node(&self, value: T) -> Node<T> {
        let mut lock = self.0.lock().unwrap();
        let next = lock.next;
        let inner = NodeInner {
            value,
            neighbors: Vec::new(),
            id: next,
        };
        
        let node = Arc::new(Mutex::new(inner));
        if next < lock.nodes.len() {
            let node_weak = Node(Arc::downgrade(&node));
            lock.nodes[next].0.replace(node.clone());
            lock.next = lock.nodes[next].1;
            node_weak
        } else {
            let node_weak = Node(Arc::downgrade(&node));
            lock.nodes.push((Some(node.clone()), next + 1));
            lock.next += 1;
            node_weak
        }
    }

    pub fn remove_node(&self, node: &Node<T>) -> Result<(), GraphError> {
        let mut lock = self.0.lock().or(Err(GraphError::LockFailure))?;
        let rc = node.0.upgrade().ok_or(GraphError::NodeDead)?;
        let id = rc.lock().unwrap().id;
        if id < lock.nodes.len() {
            let tar_node = lock.nodes[id].0.take();
            if tar_node.is_none() {
                Err(GraphError::InvalidNode)
            } else {
                lock.nodes[id].1 = lock.next;
                lock.next = id;
                Ok(())
            }
        } else {
            Err(GraphError::InvalidNode)
        }
    }
}

#[derive(Debug, Clone)]
pub struct Node<T>(Weak<Mutex<NodeInner<T>>>);

impl<T> Node<T> {
    pub fn push(&self, neighbor: &Node<T>) -> Result<(), GraphError> {
        let rc = self.0.upgrade().ok_or(GraphError::NodeDead)?;
        let mut lock = rc.lock().or(Err(GraphError::LockFailure))?;
        lock.neighbors.push(Node(neighbor.0.clone()));
        Ok(())
    }

    pub fn read<V, F>(&self, f: F) -> Result<V, GraphError> where F: Fn(&T) -> V {
        let rc = self.0.upgrade().ok_or(GraphError::NodeDead)?;
        let lock = rc.lock().or(Err(GraphError::LockFailure))?;
        let result = f(&lock.value);
        Ok(result)
    }

    pub fn write(&self, val: T) -> Result<(), GraphError> {
        let rc = self.0.upgrade().ok_or(GraphError::NodeDead)?;
        let mut lock = rc.lock().or(Err(GraphError::LockFailure))?;
        lock.value = val;
        Ok(())
    }

    pub fn modify<F>(&self, f: F) -> Result<(), GraphError> where F: Fn(&mut T) {
        let rc = self.0.upgrade().ok_or(GraphError::NodeDead)?;
        let mut lock = rc.lock().or(Err(GraphError::LockFailure))?;
        f(&mut lock.value);
        Ok(())
    }

    pub fn get_neighbors(&self) -> Result<Vec<Node<T>>, GraphError> {
        self.gc()?;
        let rc = self.0.upgrade().ok_or(GraphError::NodeDead)?;
        let lock = rc.lock().or(Err(GraphError::LockFailure))?;
        let mut result = Vec::new();
        for n in lock.neighbors.iter().filter(|n| n.is_lived()) {
            result.push(Node(n.0.clone()))
        }
        Ok(result)
    }

    fn gc(&self) -> Result<(), GraphError> {
        let rc = self.0.upgrade().ok_or(GraphError::NodeDead)?;
        let mut lock = rc.lock().or(Err(GraphError::LockFailure))?;
        let mut cleaned = Vec::new();
        for n in lock.neighbors.iter().filter(|n| n.is_lived()) {
            cleaned.push(Node(n.0.clone()))
        }
        lock.neighbors = cleaned;
        Ok(())
    }

    fn is_lived(&self) -> bool {
        self.0.strong_count() > 0
    }
}

#[derive(Debug)]
struct NodeInner<T> {
    value: T,
    neighbors: Vec<Node<T>>,
    id: usize,
}

#[cfg(test)]
mod tests {
    use crate::{Graph, GraphError};

    #[test]
    fn test_push_and_remove() {
        let graph = Graph::new();
        let node1 = graph.new_node(1);
        assert!(node1.is_lived());
        let node2 = graph.new_node(2);
        assert!(node2.is_lived());
        let node3 = graph.new_node(3);
        assert!(node3.is_lived());
        assert!(node1.push(&node2).is_ok());
        assert!(node2.push(&node3).is_ok());
        assert!(node3.push(&node1).is_ok());

        assert!(graph.remove_node(&node2).is_ok());
        assert!(graph.remove_node(&node2).is_err());
        assert!(node2.push(&node1).is_err());
        let node4 = graph.new_node(4);
        let node5 = graph.new_node(5);
        assert!(node4.is_lived());
        assert!(node5.is_lived());
        assert!(!node2.is_lived());
        assert!(node4.push(&node1).is_ok());
        assert!(node4.push(&node5).is_ok());
        assert!(node1.push(&node5).is_ok());

        assert_eq!(1, node1.get_neighbors().unwrap().len());
        assert_eq!(1, node3.get_neighbors().unwrap().len());
        assert_eq!(2, node4.get_neighbors().unwrap().len());
        assert_eq!(0, node5.get_neighbors().unwrap().len());
    }

    #[test]
    fn test_read_write() {
        let graph = Graph::new();
        let node = graph.new_node("Hello".to_owned());

        let length = node.read(|value: &String| {
            value.len()
        }).unwrap();
        assert_eq!(5, length);
        node.modify(|value: &mut String| {
            *value = "World".to_owned();
        }).unwrap();

        node.read(|value| {
            assert_eq!("World", value);
        }).unwrap();

        node.write("Hello World!".to_owned()).unwrap();
        node.read(|value| {
            assert_eq!("Hello World!", value);
        }).unwrap();
    }
}
