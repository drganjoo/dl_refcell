use std::fmt::Formatter;
use std::fmt;
use std::cell::RefCell;
use std::rc::{Rc, Weak};

/// This implements Circular Double Linked List using Rc<RefCell> just as a proof
/// of concept to check the challenges one faces in implementing such
/// a data structure in Rust

// All next links in the nodes will be strong Rcs
// All prev links in the nodes will be weak Rcs

// Even though the Link can be None, but for a ciruclar list it will 
// never be the case that the next or prev are None, but just to see how 
// more challenging it would have
// been in case these could be None 
type Link<T> = Rc<RefCell<Option<Node<T>>>>;
// all previous links will be weak RCs
type WeakLink<T> = Weak<RefCell<Option<Node<T>>>>;

#[derive(Debug)]
enum ListError {
    NodeNotFound
}

impl std::error::Error for ListError {}

impl std::fmt::Display for ListError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ListError::NodeNotFound => {
                write!(f, "Value could not be found in the list")
            }
        }
    }
}

////////////////////////////////////////////////
//  Node
////////////////////////////////////////////////

/// A node represents a node in the double linked list. For a single
/// node both next and prev would point back to the same node
struct Node<T> 
    where T : fmt::Display      // this is just for testing purposes as we print in drop
{
    data : T,
    next_node : Link<T>,
    prev_node : WeakLink<T>,
}

impl<T> Node<T> 
    where T : fmt::Display      // this is just for testing purposes as we print in drop
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

macro_rules! get_node_data {
    ($node:ident, $value:ident) => {
        let node_ref = $node.borrow();
        // the node cannot be None as the only way that is possible would be for 
        // the root node to be None and that has already been checked in the start
        // of this function
        let node_some = node_ref.as_ref().expect("Internal List issue, a 'None' node cannot be in the list");
        let $value = &node_some.data;
    };
}

// returns a cloned RC from a Weak
// a rc::Weak cannot be cloned unless it is first made into a strong 
// smart pointer
fn clone_weak_or_panic<L>(node : &Weak<L>) -> Weak<L> {
    let strong = node.upgrade().expect("The weak reference points to a location that is no longer there");
    Rc::downgrade(&strong)
}

/////////////////////////////////////////////////
//  DoubleList
/////////////////////////////////////////////////

/// The head of the DoubleList may point to a None link
/// Again, this has been done to check how more challenging it is otherwise
/// keeping an empty node would make it so much more easier to code
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

    /// iter() has been removed for now as RefCell does not offer 
    /// long term references, will figure out a way later on this
    /// to return &T not &RefCell or &Option<T>
    // pub fn iter(&self) -> ListIterator<'_, T> {
    //     ListIterator::new(Rc::clone(&self.head))
    // }

    /// Iterate over the list using next links. The passed in function is called
    /// for all nodes. In case the function returns False, the loop
    /// will not go any further
    pub fn iterate<F>(&self, f : &F)
        where F : Fn(&T) -> bool
    {
        if self.is_empty() {
            return;
        }

        let mut current = Rc::clone(&self.head);
        
        loop {
            // get the next node in the list and while the internal
            // structures are accessed, call F on the value as well
            let next = {
                let node_option = &*current.borrow();
                // the node cannot be None as the only way that is possible would be for 
                // the root node to be None and that has already been checked in the start
                // of this function
                let node_some = node_option.as_ref().expect("Internal List issue, a 'None' node cannot be in the list");
                let value = &node_some.data;

                if !f(&value) {
                    break;
                }

                // clone the next strong link and save that for next call
                Rc::clone(&node_some.next_node)
            };

            current = next;

            // in case we have come back to the root node, we need to end the loop
            if &*current as *const _ == &*self.head as *const _ {
                break;
            }
        }
    }

    fn visit_each_node<F>(&self, f : &F) 
        where F : Fn(&Link<T>) -> bool
    {
        if self.is_empty() {
            return;
        }

        let mut current = Rc::clone(&self.head);
        
        loop {
            // get the next node in the list and while the internal
            // structures are accessed, call F on the value as well
            let next = {
                if !f(&current) {
                    break;
                }

                let node_option = &*current.borrow();
                // the node cannot be None as the only way that is possible would be for 
                // the root node to be None and that has already been checked in the start
                // of this function
                let node_some = node_option.as_ref().expect("Internal List issue, a 'None' node cannot be in the list");
                // clone the next strong link and save that for next call
                Rc::clone(&node_some.next_node)
            };

            current = next;

            // in case we have come back to the root node, we need to end the loop
            if &*current as *const _ == &*self.head as *const _ {
                break;
            }
        }
    }

    /// Iterate over the list using prev links. The passed in function is called
    /// for all nodes. In case the function returns False, the loop
    /// will not go any further
    pub fn iterate_rev<F>(&self, f : &F)
        where F : Fn(&T) -> bool
    {
        if self.is_empty() {
            return;
        }

        let head_ref = &self.head.borrow();
        let head_some = head_ref.as_ref().expect("Head cannot be None as that has already been checked");
        let tail = &head_some.prev_node;
        let tail_strong = tail.upgrade().expect("Internal list implementaiton issue. Tail is dangling.");

        let mut current = Rc::clone(&tail_strong);
        let end_marker = Rc::clone(&tail_strong);
        
        loop {
            // get the prev node in the list and while the internal
            // structures are accessed, call F on the value as well
            let prev = {
                let node_option = &*current.borrow();
                // the node cannot be None as the only way that is possible would be for 
                // the root node to be None and that has already been checked in the start
                // of this function
                let node_some = node_option.as_ref().expect("Internal List issue, a 'None' node cannot be in the list");
                let value = &node_some.data;

                if !f(&value) {
                    break;
                }

                // clone the next strong link and save that for next call
                let prev_strong = node_some.prev_node.upgrade().expect("Internal List issue. Prev node is dangling");
                Rc::clone(&prev_strong)
            };

            current = prev;

            // in case we have come back to the root node, we need to end the loop
            if &*current as *const _ == &*end_marker as *const _ {
                break;
            }
        }
    }

    /// inserts an element at the start of the list
    pub fn insert_front(&mut self, new_data : T) {
        // create a node with the given element
        let mut new_node = Node::new(new_data);

        // in case the head is dangling, set the new node as the head
        let new_head = match &mut *self.head.borrow_mut() {
            None => {
                // make the node's next and prev point back to the same node
                // we could have written node_rc = Rc::new(RefCell::new(new_noe))
                // but to get the next / prev out of the node to set them back to itself
                // we would need to unwrap on RefCell.borrow(). So it is easier
                // to set the node_rc to empty, change new_now and then replace RefCell
                // to have new_node in it
                let node_rc = Rc::new(RefCell::new(None));
                
                new_node.next_node = Rc::clone(&node_rc);
                new_node.prev_node = Rc::downgrade(&node_rc);
    
                // put the new node in the refcell we just created
                *node_rc.borrow_mut() = Some(new_node);
    
                node_rc
            },
            Some(head_node) => {
                // since the root node already exists we need to make the new node as the root
                // and make following connections:
                //  new->prev = head->prev (tail)
                //  new->next = head
                //  tail->next = new node
                //  head->prev = new node

                let tail = &head_node.prev_node;

                // new node's prev will be the tail of the list
                new_node.prev_node = clone_weak_or_panic(tail);

                // new node's next is going to be the current head
                new_node.next_node = Rc::clone(&self.head);

                let new_head = Rc::new(RefCell::new(Some(new_node)));
                
                // tails's next is going to be the new head
                let tail_strong = tail.upgrade().expect("Tail refers to a dangling pointer");

                // tail->next has to be the new node BUT
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

    /// inserts an element at the end of the list
    pub fn insert_back(&mut self, new_data : T) {
        // on an empty list just call the insert_front to handle
        // special case of changing head it self
        if self.is_empty() {
            self.insert_front(new_data);
            return;
        }

        // create a node with the given element
        let mut new_node = Node::new(new_data);

        // since the head and the tail can be the same, we don't want to 
        // borrow a reference to the head and then get to the tail as when
        // will call borrow_mut on tail it will panic. So take a limited
        // borrow and clone the tail link into a strong RC
        let tail = {
            let head_ref = &self.head.borrow();
            let head_some = head_ref.as_ref().expect("Head Node cannot be None as we have already tested this");
            let tail_strong = head_some.prev_node.upgrade().expect("List implementation error. Head's prev cannot be None");
            Rc::clone(&tail_strong)
        };

        // the following operations have to be carried out
        // new->prev = tail
        // new->next = head
        // tail->next = new node
        // head->prev = new node
        new_node.prev_node = Rc::downgrade(&tail);
        new_node.next_node = Rc::clone(&self.head);

        let new_node_rc = Rc::new(RefCell::new(Some(new_node)));

        // tail->next = new node
        let mut tail_ref = tail.borrow_mut();
        let tail_some = &mut tail_ref.as_mut().expect("List implementation error, tail cannot be None");

        tail_some.next_node = Rc::clone(&new_node_rc);

        // head->prev = new node
        let mut head_ref = self.head.borrow_mut();
        let head_some = &mut head_ref.as_mut().expect("List implementation error, tail cannot be None");

        head_some.prev_node = Rc::downgrade(&new_node_rc);
    }

    pub fn delete(&mut self, value : &T) -> Result<(), ListError> {
        if self.is_empty() {
            return Err(ListError::NodeNotFound);
        }

        let mut current = Rc::clone(&self.head);
        let end_marker = Rc::clone(&self.head);

        let mut found = false;
        let mut is_single = false;

        loop {
            let next = {
                let current_ref = current.borrow();
                let current_some = current_ref.as_ref().expect("List implementation error. Head is None after checking is_empty");
                if current_some.data == *value {
                    found = true;
                    is_single = &current_some.next_node.borrow() as *const _ == &current_ref as *const _;
                    break;
                }

                if &*current as *const _ == &*end_marker as *const _ {
                    // we've come back to the end_marker
                    break;
                }

                Rc::clone(&current_some.next_node)
            };

            current = next;
        }

        if found {
            // in case of sinle node just set head to None
            let is_head = &*current as *const _ == &*self.head as *const _;

            if is_single {
                let mut head = self.head.borrow_mut();
                {
                    let head_some = head.as_ref().expect("List implementation error. Head has None");

                    // break the next link of the only head node
                    let mut next_ref = head_some.next_node.borrow_mut();
                    *next_ref = None;
                }

                // set head to point to None
                *head = None;
            }
            else {
                // node found and needs to be deleted
                // prev->next = current->next
                // current->next = current->prev
                let mut current_ref = current.borrow_mut();
                let current_some = current_ref.as_mut().expect("List implementation error. Current has no node");

                let next = Rc::clone(&current_some.next_node);

                // break the next link of the current->next
                current_some.next_node = Rc::new(RefCell::new(None));
            
                // prev->next = current->next
                let prev = &current_some.prev_node;
                let prev_strong = prev.upgrade().expect("List implementation error. Prev is dangling");

                let mut prev_ref = prev_strong.borrow_mut();
                let prev_some = prev_ref.as_mut().expect("List implementation error. Prev is None");
                prev_some.next_node = Rc::clone(&next);

                // current->next = current->prev
                let mut next_ref = next.borrow_mut();
                let next_some = next_ref.as_mut().expect("List implementation error. Next is None");
                next_some.prev_node = Rc::downgrade(&prev_strong);

                if is_head {
                    self.head = Rc::clone(&next);
                }
            }

            return Ok(())
        }

        Err(ListError::NodeNotFound)
    }

    pub fn print_counts(&self) {
        self.visit_each_node(&|node : &Link<T>| {
            get_node_data!(node, value);
            println!("{}, Strong: {}, Weak: {}", value, Rc::strong_count(&node), Rc::weak_count(&node));
            return true;
        });
    }
}

/// All next links are strong and prev links are weak. However, the
/// first node of the list has two strong Rcs to it. The tail->next
/// has a strong link to it and self.head has a strong link to it. 
/// Drop of DoubleList has to remove tail's strong link. The head 
/// will be dropped by Rust's allocator
impl<T> Drop for DoubleList<T> 
    where T : fmt::Display
{
    fn drop(&mut self) { 
        // nothing to do in case of empty list
        if self.head.borrow().is_none() {
            return;
        }

        // the tail is maintaing a strong reference to the head, 
        // that needs to be removed
        if let Some(ref mut head_node) = &mut *self.head.borrow_mut() {
            let tail = &head_node.prev_node;
            let tail_strong = &tail.upgrade().expect("Tail cannot be None. Something went wrong");
            let mut tail_node_ref = tail_strong.borrow_mut();
            let tail_node_some = tail_node_ref.as_mut().expect("Tail node can never be None. Check links");
            
            tail_node_some.next_node = Rc::new(RefCell::new(None));
        }
    }
}

fn check() {
    let mut d = DoubleList::<i32>::new();
    d.insert_front(32);
    d.print_counts();

    d.insert_front(3);
    d.insert_back(13);

    d.print_counts();

    d.iterate(&|value : &i32| -> bool {
        println!("{}", value);
        return true;
    });

    println!("calling reverse:");
    d.print_counts();
    d.delete(&3).ok();
    d.print_counts();

    d.iterate_rev(&|value : &i32| -> bool {
        println!("{}", value);
        return true;
    });
}

fn main() {
    check();
    println!("All nodes should have been dropped");
}

#[cfg(test)]
mod test {
    use rand::Rng;
    use super::*;

    #[test]
    fn empty_iter() {
        let mut list : DoubleList<i32> = DoubleList::new();
        list.iterate(&|v : &i32|{
            assert!(false, "It should not have called on an empty list");
            return true;
        });
    }

    #[test]
    fn single_node_iter() {
        let mut list : DoubleList<i32> = DoubleList::new();
        list.insert_back(13);

        let mut times_called = 0;
        list.iterate(&move |v : &i32|{
            times_called += 1;
            assert!(times_called == 1, "It should not have called more than once");
            return true;
        });
    }

    #[test]
    fn single_node_iter_front() {
        let mut list : DoubleList<i32> = DoubleList::new();
        list.insert_front(19);

        let mut times_called = 0;
        list.iterate(&move |v : &i32|{
            times_called += 1;
            assert!(times_called == 1, "It should not have called more than once");
            return true;
        });
    }

    #[test]
    fn test_insert_front() {
        let sample = vec![1,4,43, 9, 3, 56, 4];

        let mut list : crate::DoubleList<i32> = crate::DoubleList::new();
        for s in &sample {
            list.insert_front(*s);
        }

        test_forward(&sample, &list);
        test_reverse(&sample, &list);
    }

    #[test]
    fn test_insert_back() {
        let mut rng = rand::thread_rng();
        let mut sample : Vec<i32> = Vec::with_capacity(64);

        for _ in 0..64 {
            let x : i32 = rng.gen();
            sample.push(x);
        }

        let mut list : crate::DoubleList<i32> = crate::DoubleList::new();
        for s in &sample {
            list.insert_back(*s);
        }

        // the two functions test_forward and test_reverse were written
        // from the insert_front angle so we need to reverse the sample list
        sample.reverse();
        // test if they match
        test_forward(&sample, &list);
        test_reverse(&sample, &list);
    }

    fn test_forward<T>(sample : &Vec<T>, list : &crate::DoubleList<T>) 
        where T : std::fmt::Display + std::fmt::Debug + std::cmp::PartialEq
    {
        let mut i = sample.len() - 1;
        list.iterate(&move |x : &T| {
            assert_eq!(*x, sample[i]);
            if i > 0 {
                i -= 1;
            }
            return true;
        });
    }

    fn test_reverse<T>(sample : &Vec<T>, list : &crate::DoubleList<T>) 
        where T : std::fmt::Display + std::fmt::Debug + std::cmp::PartialEq
    {
        let mut i = 0;
        list.iterate_rev(&move |x : &T| {
            assert_eq!(*x, sample[i]);
            if i > 0 {
                i -= 1;
            }
            return true;
        });
    }

    /// checks if returning a double list from a function works
    #[test]
    fn test_ret_from_fn() {
        let sample = vec![1,4,43, 4, 5, 7, 9, 10, 11];
        let list = add_to_list(&sample);

        test_forward(&sample, &list);
        test_reverse(&sample, &list);
    }

    fn add_to_list(sample : &Vec<i32>) -> crate::DoubleList<i32> {
        let mut list : crate::DoubleList<i32> = crate::DoubleList::new();
        for s in sample {
            list.insert_front(*s);
        }

        list
    }

    /// checks if returning a double list from a function works
    #[test]
    fn test_delete() {
        let mut sample = vec![1,4,43, 4, 5, 7, 9, 10, 11];
        let mut list = add_to_list(&sample);
        
        assert_eq!(list.delete(&43), true);
        assert_eq!(list.delete(&1043), false);

        sample.remove(2);

        test_forward(&sample, &list);
        test_reverse(&sample, &list);
    }
}