use std::fmt;
use std::cell::RefCell;
use std::rc::{Rc, Weak};
use std::marker::PhantomData;

type Link<T> = RefCell<Option<Rc<Node<T>>>>;
type WeakLink<T> = RefCell<Option<Weak<Node<T>>>>;

struct Node<T> 
    where T : fmt::Display
{
    data : T,
    next_node : Link<T>,
    prev_node : WeakLink<T>,
}

impl<T> Node<T> 
    where T : fmt::Display
{
    fn new(with_data : T) -> Self {
        Node {
            data : with_data,
            next_node : RefCell::new(None),
            prev_node : RefCell::new(None)
        }
    }
}

impl<T> Drop for Node<T> 
    where T : fmt::Display
{
    fn drop(&mut self) { 
        println!("Node with value {} is being dropped", self.data);
    }
}

struct DoubleList<T> 
    where T : fmt::Display
{
    head : Link<T>
}

impl<T> DoubleList<T> 
    where T : fmt::Display + PartialEq
{
    pub fn new() -> Self {
        DoubleList {
            head : RefCell::new(None)
        }
    }

    /// is the list empty?
    pub fn is_empty(&self) -> bool {
        self.head.borrow().is_none()
    }

    /// returns an iterator on the elements
    pub fn iter(&self) -> ListIterator<'_, T> {
        ListIterator::new(&self.head)
    }
    
    /// inserts an element at the start of the list
    pub fn insert_front(&mut self, new_data : T) {
        // create a node with the given element
        let node = Node::new(new_data);

        // in case the head is dangling, set the new node as the head
        // make it circular on itself
        if self.is_empty() {
            let node_rc = Rc::new(node);
            *(*node_rc).next_node.borrow_mut() = Some(Rc::clone(&node_rc));
            *(*node_rc).prev_node.borrow_mut() = Some(Rc::downgrade(&node_rc));

            let mut head = self.head.borrow_mut();
            *head = Some(node_rc);
        }
        else {

        }
    }
}

impl<T> Drop for DoubleList<T> 
    where T : fmt::Display
{
    fn drop(&mut self) { 
        println!("Double list is being dropped");
    }
}

/// Returns an iterator on the list
pub struct ListIterator<'a, T> 
    where T: fmt::Display
{
    //head_ptr : &'a Option<Rc<Node<T>>>,
    head_ptr : &'a Link<T>,
    iter_ptr : Option<Rc<Node<T>>>,
    dead_end : Link<T>
}

impl<'a, T> ListIterator<'a, T> 
    where T : fmt::Display
{
    // creates a new iterator. For emtpy list the current node
    // is set to dangling
    fn new(head_ptr : &'a Link<T>) -> Self{
        let current = match *head_ptr.borrow() {
            None => None,
            Some(node) => Some(Rc::clone(&node))
        };

        ListIterator {
            head_ptr : head_ptr,
            iter_ptr : current,
            dead_end : RefCell::new(None)
        }
    }
}

impl<'a, T> Iterator for ListIterator<'a, T> 
    where T : fmt::Display
{
    type Item = &'a T;
    
    fn next(&mut self) -> Option<Self::Item> { 
        match self.iter_ptr {
            None => return None,
            Some(node) => {
                let value = &node.data;

                // set the next node based on the next link of the node being
                // visited at the moment
                if let Some(next_rc) = &*node.next_node.borrow() {
                    if let Some(head_rc) = &self.head_ptr.borrow() {
                        let head_rc : &Rc<Node<T>> = 
                        let head_ptr = &**head_rc as *const _;
                        let next_ptr = &**next_rc as *const _;

                        if next_ptr == head_ptr {
                            self.iter_ptr = None
                        }
                        else {
                            self.iter_ptr = Some(Rc::clone(&next_rc));
                        }
                    }
                }
                return Some(value);
            }
        }
    }
}


fn main() {
    let mut d = DoubleList::<i32>::new();
    d.insert_front(32);

    for i in d.iter() {
        println!("{}", i);
    }
}
