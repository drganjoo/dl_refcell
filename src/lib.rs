use std::fmt::Formatter;
use std::fmt;
use std::cell::RefCell;
use std::rc::{Rc, Weak};

#[macro_use]
mod macros;

/// This implements Circular Double Linked List using Rc<RefCell> just as a proof
/// of concept to check the challenges one faces in implementing such
/// a data structure in Rust

// All next links in the nodes will be strong Rcs
// All prev links in the nodes will be weak Rcs

// Even though the Link can be None, but for a ciruclar list it will 
// never be the case that the next or prev are None. For a ciruclar list, a single node
// will point to itself. Buf just to see how more challenging it would have been
// in case we were not implementing a Circular List the Option has been used as part of Link.
type Link<T> = Rc<RefCell<Option<Node<T>>>>;
// all previous links will be weak RCs
type WeakLink<T> = Weak<RefCell<Option<Node<T>>>>;

/// An ListError is returned from delete in case an element that is to be deleted
/// cannot be found
#[derive(Debug)]
pub enum ListError {
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
        // by default the next and prev are set to None
        Node {
            data : with_data,
            next_node : Rc::new(RefCell::new(None)),
            prev_node : Rc::downgrade(&Rc::new(RefCell::new(None))),
        }
    }
}

/// Drop on a Node is only implemented to show which nodes have been dropped
/// to ensure that all nodes eventually get dropped
#[cfg(debug_assertions)]
impl<T> Drop for Node<T> 
    where T : fmt::Display
{
    fn drop(&mut self) { 
        // let go of the strong link that node maintains to the next
        println!("Node with value {} is being dropped", self.data);
    }
}

// returns a cloned RC from a Weak one
// A rc::Weak cannot be cloned unless it is first made into a strong 
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
pub struct DoubleList<T> 
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
        // for each node call the callback funciton. stop if the callback
        // returns false any time
        visit_each_node!(&self.head, link, {
            // get the data for the node
            get_node_from_link!(link, node);
            // call the callback and stop in case it returns false
            if !f(&node.data) {
                break;
            }
        });
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

        get_prev_strong_clone!(self.head, end_marker);

        let mut current = Rc::clone(&end_marker);
        
        loop {
            // get node from the link, call F on it and then get a strong
            // RC link to the prev of that node
            let prev = {
                get_node_from_link!(current, node);

                if !f(&node.data) {
                    break;
                }

                // clone the next strong link and save that for next call
                get_prev_strong_clone!(current, prev);

                // end the borrow of current and return the prev
                prev
            };

            current = prev;

            // in case we have come back to the root node, we need to end the loop
            if Rc::ptr_eq(&current, &end_marker) {
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
                if Rc::ptr_eq(&tail_strong, &self.head) {
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
        get_prev_strong_clone!(self.head, tail);

        // the following operations have to be carried out
        // new->prev = tail
        // new->next = head
        // tail->next = new node
        // head->prev = new node
        new_node.prev_node = Rc::downgrade(&tail);
        new_node.next_node = Rc::clone(&self.head);

        let new_node_rc = Rc::new(RefCell::new(Some(new_node)));

        // tail->next = new node
        {
            get_node_mut_from_link!(tail, tail_some);
            tail_some.next_node = Rc::clone(&new_node_rc);
        }

        // head->prev = new node
        get_node_mut_from_link!(self.head, head_some);
        head_some.prev_node = Rc::downgrade(&new_node_rc);
    }

    /// deletes the given value from the list if it is found OR ListError is returned
    pub fn delete(&mut self, value : &T) -> Result<(), ListError> {
        let mut found = false;
        
        // find the given node and then delete it
        visit_each_node!(&self.head, link, {
            let should_delete = {
                get_node_from_link!(link, node);
                node.data == *value
            };

            if should_delete {
                self.delete_link(&link);
                found = true;
                break;
            }
        });

        if !found {
            return Err(ListError::NodeNotFound);
        }

        Ok(())
    }

    fn delete_link(&mut self, delete_link : &Link<T>) {
        // figure out if the head node is to be deleted?
        let is_only_head = {
            get_node_from_link!(delete_link, node);
            
            Rc::ptr_eq(&delete_link, &self.head) 
            &&  Rc::ptr_eq(&node.next_node, &self.head)
        };

        if is_only_head {
            let mut head = self.head.borrow_mut();
            // break the next link of the only head node
            let head_some = head.as_mut().expect("List implementation error. Head has None");
            head_some.next_node = Rc::new(RefCell::new(None));

            // set head to point to None
            *head = None;
        }
        else {
            // prev->next = current->next
            // current->next->prev = current->prev

            // the following code borrows / mut_borrows from different links
            // using small blocks so that the borrow ends before we try to get
            // next borrow / mut on it.

            // break link to current->next node while keeping mutable borrow
            // to the smallest possible block.
            let next = {
                get_node_mut_from_link!(delete_link, current_some);

                // keep a pointer on next before it gets dropped due to our link break
                let next = Rc::clone(&current_some.next_node);
                current_some.next_node = Rc::new(RefCell::new(None));

                next
            };

            // set prev->next = current->next
            // In a 2 node double list, the prev link points to the next. So we need
            // to be careful with the mutable borrows we might have taken on the next
            let prev = {
                get_prev_strong_clone!(delete_link, prev_strong);
                get_node_mut_from_link!(prev_strong, prev_node);

                prev_node.next_node = Rc::clone(&next);

                Rc::downgrade(&prev_strong)
            };

            // set current->next->prev = current->prev
            {
                get_node_mut_from_link!(next, next_node);
                next_node.prev_node = prev;
            }

            // change head if that is the node we just deleted
            let is_head = Rc::ptr_eq(&delete_link, &self.head);
            if is_head {
                self.head = Rc::clone(&next);
            }
        }
    }

    /// debug routeine to print strong and weak counts. Since the routine
    /// itself takes a strong link to the node, the strong counts are + 1
    /// from what they actually would have been
    pub fn print_counts(&self) {
        visit_each_node!(&self.head, link, {
            get_node_from_link!(link, node);
            println!("{}, Strong: {}, Weak: {}", node.data, Rc::strong_count(&link), Rc::weak_count(&link));
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
        // the tail is maintaing a strong reference to the head, 
        // that needs to be removed
        if let Some(ref mut head_node) = &mut *self.head.borrow_mut() {
            let tail = &head_node.prev_node;
            let tail_strong = &tail.upgrade().expect("Tail cannot be None. Something went wrong");

            // in case the tail node is different from the head node
            if !Rc::ptr_eq(&tail_strong, &self.head) {
                let mut tail_node_ref = tail_strong.borrow_mut();
                let tail_node_some = tail_node_ref.as_mut().expect("Tail node can never be None. Check links");
                tail_node_some.next_node = Rc::new(RefCell::new(None));
            }
            else {
                head_node.next_node = Rc::new(RefCell::new(None));
            }
        }
    }
}

#[cfg(test)]
mod test {
    use rand::Rng;
    use super::*;

    #[test]
    fn empty_iter() {
        let list : DoubleList<i32> = DoubleList::new();
        list.iterate(&|_v : &i32|{
            assert!(false, "It should not have called on an empty list");
            return true;
        });
    }

    #[test]
    fn single_node_iter_back() {
        let mut list : DoubleList<i32> = DoubleList::new();
        list.insert_back(13);

        let times = Rc::new(RefCell::new(0));
        let times_called = times.clone();
        list.iterate(&move |_v : &i32|{
            *times_called.borrow_mut() += 1;
            return true;
        });

        assert!(*times.borrow() == 1, "It should not have called more than once");
    }

    #[test]
    fn single_node_iter_front() {
        let mut list : DoubleList<i32> = DoubleList::new();
        list.insert_front(19);

        let times = Rc::new(RefCell::new(0));
        let times_called = times.clone();

        list.iterate(&move |_v : &i32|{
            *times_called.borrow_mut() += 1;
            return true;
        });

        assert!(*times.borrow() == 1, "It should not have called more than once");
    }

    #[test]
    fn test_insert_front() {
        let mut sample = vec![1,4,43, 9, 3, 56, 4];

        let mut list : crate::DoubleList<i32> = crate::DoubleList::new();
        for s in &sample {
            list.insert_front(*s);
        }

        test_forward(&sample, &list);
        sample.reverse();
        test_reverse(&sample, &list);
    }

    #[test]
    fn test_insert_back() {
        let mut rng = rand::thread_rng();
        let count = 2;
        let mut sample : Vec<i32> = Vec::with_capacity(count);

        for _ in 0..count {
            let x : i32 = rng.gen();
            sample.push(x);
        }

        let mut list : crate::DoubleList<i32> = crate::DoubleList::new();
        for s in &sample {
            list.insert_back(*s);
        }

        // the two functions test_forward and test_reverse were written
        // from the insert_front angle so we need to reverse the sample list
        test_reverse(&sample, &list);
        sample.reverse();
        test_forward(&sample, &list);
    }

    fn test_forward<T>(sample : &Vec<T>, list : &crate::DoubleList<T>) 
        where T : std::fmt::Display + std::fmt::Debug + std::cmp::PartialEq
    {
        let count = Rc::new(RefCell::new(sample.len() - 1));

        list.iterate(&move |x : &T| {
            let mut i = count.borrow_mut();
            assert_eq!(*x, sample[*i]);

            if *i > 0 {
                *i -= 1;
            }

            return true;
        });
    }

    fn test_reverse<T>(sample : &Vec<T>, list : &crate::DoubleList<T>) 
        where T : std::fmt::Display + std::fmt::Debug + std::cmp::PartialEq
    {
        let count = Rc::new(RefCell::new(sample.len() - 1));
        list.iterate_rev(&move |x : &T| {
            let mut i = count.borrow_mut();

            assert_eq!(*x, sample[*i]);
            if *i > 0 {
                *i -= 1;
            }
            return true;
        });
    }

    /// checks if returning a double list from a function works
    #[test]
    fn test_ret_from_fn() {
        let mut sample = vec![1,4,43, 4, 5, 7, 9, 10, 11];
        let list = add_to_list(&sample);

        test_forward(&sample, &list);
        sample.reverse();
        test_reverse(&sample, &list);
    }

    fn add_to_list(sample : &Vec<i32>) -> crate::DoubleList<i32> {
        let mut list : crate::DoubleList<i32> = crate::DoubleList::new();
        for s in sample {
            list.insert_front(*s);
        }

        list
    }
}
