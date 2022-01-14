use dl_refcell::DoubleList;

fn check() {
    let mut d = DoubleList::<i32>::new();
    d.insert_front(32);
    d.delete(&32).ok();

    d.insert_front(32);
    d.insert_front(3);
    d.insert_back(13);

    d.print_counts();

    d.iterate(&|value : &i32| -> bool {
        println!("{}", value);
        true
    });

    println!("calling reverse:");
    d.print_counts();
    d.delete(&3).ok();
    d.print_counts();
    d.delete(&32).ok();
    d.delete(&13).ok();
    d.delete(&3).err();

    d.print_counts();
    
    d.insert_back(100);
    d.insert_back(200);
    d.insert_back(300);
    d.insert_back(400);
    d.insert_back(500);

    d.iterate(&|value : &i32| -> bool {
        println!("{}", value);
        true
    });

    d.delete(&300).ok();

    d.iterate_rev(&|value : &i32| -> bool {
        println!("{}", value);
        true
    });
}

fn main() {
    check();
    println!("All nodes should have been dropped");
}

