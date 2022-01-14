macro_rules! get_node_from_link {
    ($node:expr, $value:ident) => {
        let node_ref = $node.borrow();
        // the node cannot be None as the only way that is possible would be for 
        // the root node to be None and that has already been checked in the start
        // of this function
        let node_some = node_ref.as_ref().expect("Internal List issue, a 'None' node cannot be in the list");
        let $value = &node_some;
    };
}

macro_rules! get_node_mut_from_link {
    ($node:expr, $value:ident) => {
        let mut node_ref = $node.borrow_mut();
        // the node cannot be None as the only way that is possible would be for 
        // the root node to be None and that has already been checked in the start
        // of this function
        let $value = node_ref.as_mut().expect("Internal List issue, a 'None' node cannot be in the list");
    };
}

macro_rules! get_prev_strong_clone {
    ($node:expr, $strong_clone:ident) => {
        let $strong_clone = {
            let node_ref = $node.borrow();
            let node_some = node_ref.as_ref().expect("Head Node cannot be None as we have already tested this");
            let strong = node_some.prev_node.upgrade().expect("List implementation error. Head's prev cannot be None");
            Rc::clone(&strong)
        };
    }
}

macro_rules! visit_each_node {
    ($start: expr, $current: ident, $f : block) => {
        {
            let any_nodes = $start.borrow().is_some();

            if any_nodes {
                let mut $current = Rc::clone(&$start);
                
                loop {
                    // get the next node in the list and while the internal
                    // structures are accessed, call F on the value as well
                    let next = {
                        $f
                        
                        get_node_from_link!($current, node_some);
                        Rc::clone(&node_some.next_node)
                    };

                    $current = next;

                    // in case we have come back to the root node, we need to end the loop
                    if Rc::ptr_eq(&$current, &$start) {
                        break;
                    }
                }
            }
        }
    };
}
