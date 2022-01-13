use std::marker::PhantomData;
use std::fmt;
use std::cell::RefCell;
use std::rc::{Rc, Weak};

type Link<T> = Rc<RefCell<Option<Node<T>>>>;
type WeakLink<T> = Weak<RefCell<Option<Node<T>>>>;

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
            next_node : Rc::new(RefCell::new(None)),
            prev_node : Rc::downgrade(&Rc::new(RefCell::new(None))),
        }
    }
}

impl<T> Drop for Node<T> 
    where T : fmt::Display
{
    fn drop(&mut self) { 
        // let go of the strong link that node maintains to the next
        println!("Node with value {} is being dropped", self.data);
    }
}

fn clone_weak_or_panic<L>(node : &Weak<L>) -> Weak<L> {
    let strong = node.upgrade().expect("The weak reference points to a location that is no longer there");
    Rc::downgrade(&strong)
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
            head : Rc::new(RefCell::new(None))
        }
    }

    /// is the list empty?
    pub fn is_empty(&self) -> bool {
        self.head.borrow().is_none()
    }

    /// returns an iterator on the elements
    // pub fn iter(&self) -> ListIterator<'_, T> {
    //     ListIterator::new(Rc::clone(&self.head))
    // }

    pub fn print(&self) {
        if self.is_empty() {
            return;
        }

        let mut current = Rc::clone(&self.head);
        
        loop {
            let next = {
                let node_option = &*current.borrow();
                let node_some = node_option.as_ref().expect("A None node cannot be in the list");
                let value = &node_some.data;

                println!("{}", value);

                Rc::clone(&node_some.next_node)
            };

            current = next;

            if &*current as *const _ == &*self.head as *const _ {
                break;
            }
        }
    }
    
    /// inserts an element at the start of the list
    pub fn insert_front(&mut self, new_data : T) {
        // create a node with the given element
        let mut new_node = Node::new(new_data);

        // in case the head is dangling, set the new node as the head
        // make it circular on itself
        let new_head = match &mut *self.head.borrow_mut() {
            None => {
                let node_ref = RefCell::new(None);
                let node_rc = Rc::new(node_ref);
                
                new_node.next_node = Rc::clone(&node_rc);
                new_node.prev_node = Rc::downgrade(&node_rc);
    
                *node_rc.borrow_mut() = Some(new_node);
    
                node_rc
            },
            Some(head_node) => {
                let tail = &head_node.prev_node;

                // new node's prev will be the tail of the list
                new_node.prev_node = clone_weak_or_panic(tail);

                // new node's next is going to be the current head
                new_node.next_node = Rc::clone(&self.head);

                let new_head = Rc::new(RefCell::new(Some(new_node)));
                
                // tails's next is going to be the new head
                let tail_strong = tail.upgrade().expect("Tail refers to a dangling pointer");

                // when there is only one root node then the tail and head are same
                // and we already have a mutable reference to the head so we cannot
                // take another mutable reference to the tail in that case.
                if &*tail_strong as *const _ == &*self.head as *const _ {
                    head_node.next_node = Rc::clone(&new_head);
                }
                else {
                    let mut tail_node_ref = tail_strong.borrow_mut();
                    let tail_node_some = tail_node_ref.as_mut().expect("Tail node can never be None. Check links");

                    tail_node_some.next_node = Rc::clone(&new_head);
                }

                // old head's prev is going to be the new node
                head_node.prev_node = Rc::downgrade(&new_head);

                new_head
            }
        };

        self.head = new_head;
    }
}

impl<T> Drop for DoubleList<T> 
    where T : fmt::Display
{
    fn drop(&mut self) { 
        // the tail is maintaing a strong reference to the head, 
        // that needs to be removed
        if let Some(ref mut head_node) = &mut *self.head.borrow_mut() {
            let tail = &head_node.prev_node;
            let tail_strong = &tail.upgrade().expect("Tail cannot be None. Something went wrong");
            let mut tail_node_ref = tail_strong.borrow_mut();
            let tail_node_some = tail_node_ref.as_mut().expect("Tail node can never be None. Check links");
            
            tail_node_some.next_node = Rc::new(RefCell::new(None));
        }

        println!("Double list is being dropped");
    }
}

/// Returns an iterator on the list
pub struct ListIterator<'a, T> 
    where T: fmt::Display
{
    //head_ptr : &'a Option<Rc<Node<T>>>,
    head_ptr : Link<T>,
    iter_ptr : Link<T>,
    _phantom : PhantomData<&'a T>
}

// impl<'a, T> ListIterator<'a, T> 
//     where T : fmt::Display
// {
//     // creates a new iterator. For emtpy list the current node
//     // is set to dangling
//     fn new(head_ptr : Link<T>) -> Self{
//         ListIterator {
//             head_ptr : head_ptr,
//             iter_ptr : Rc::clone(&head_ptr),
//             _phantom : PhantomData {}
//         }
//     }
// }

// impl<'a, T> Iterator for ListIterator<'a, T> 
//     where T : fmt::Display
// {
//     type Item = &'a T;
    
//     fn next(&mut self) -> Option<Self::Item> { 
//         match &*self.iter_ptr.borrow() {
//             None => None,
//             Some(node) => {
//                 Some(&node.data)
//             }
//         }
//     }
// }

fn check() {
    let mut d = DoubleList::<i32>::new();
    d.insert_front(32);
    d.insert_front(3);
    d.print();
}

fn main() {
    check();
    println!("All nodes should have been dropped");
}
