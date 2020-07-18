#![allow(unused_imports)]
#![allow(unused_variables)]
use nanoda_lib::utils::{ Env, List,  List::* };
use nanoda_lib::name::Name;
use nanoda_lib::level::{ LevelsPtr, Level, Level::* };
use nanoda_lib::param;
use nanoda_lib::trace::NoopTracer;

#[test]
fn util_test0() {
    let mut env = Env::new(NoopTracer);
    let mut env2 = Env::new(NoopTracer);
    let target = Zero.alloc(&mut env2)
                     .new_succ(&mut env2)
                     .new_succ(&mut env2)
                     .new_succ(&mut env2)
                     .new_succ(&mut env2)
                     .new_succ(&mut env2);

    let env_five;
    {
        let z = Zero.alloc(&mut env);
        let one = z.new_succ(&mut env);
        let two = one.new_succ(&mut env);

        let mut live = env.as_live();

        let three = two.new_succ(&mut live);
        let four = three.new_succ(&mut live);
        let five = four.new_succ(&mut live);

        env_five = five.insert_env(&mut live.env, &live.store);
    }


    assert_eq!(env_five, target)
}



#[test]
fn util_test2() {
    let mut env = Env::new(NoopTracer);
    let mut env = env.as_live();

    let l1 = param!(["u", "v"], &mut env);
    let p1 = param!("u", &mut env);
    let (r, _hmem) = p1.pos(l1, &mut env);
    assert_eq!(Some(0), r);
}


#[test]
fn pos_test0() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let l = param!(["a", "b", "c", "d", "e"], &mut live);

    let param_a = param!("a", &mut live);
    let param_b = param!("b", &mut live);
    let param_c = param!("c", &mut live);
    let param_d = param!("d", &mut live);
    let param_e = param!("e", &mut live);
    let param_z = param!("z", &mut live);

    assert_eq!(param_a.pos(l, &mut live).0, Some(0));
    assert_eq!(param_b.pos(l, &mut live).0, Some(1));
    assert_eq!(param_c.pos(l, &mut live).0, Some(2));
    assert_eq!(param_d.pos(l, &mut live).0, Some(3));
    assert_eq!(param_e.pos(l, &mut live).0, Some(4));
    assert_eq!(param_z.pos(l, &mut live).0, None);
}


#[test]
fn concat_test0() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let l1 = param!(["a", "b"], &mut live);

    let l2 = param!(["c", "d"], &mut live);

    let target = param!(["a", "b", "c", "d"], &mut live);
    assert_eq!(l1.concat(l2, &mut live), target);
}


#[test]
fn concat_test1() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let l1 = param!(["a", "b"], &mut live);
    let l2 = Nil::<Level>.alloc(&mut live);
    let target = param!(["a", "b"], &mut live);
    assert_eq!(l1.concat(l2, &mut live), target);

}
#[test]
fn concat_test2() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let l1 = Nil::<Level>.alloc(&mut live);
    let l2 = param!(["a", "b"], &mut live);
    let target = param!(["a", "b"], &mut live);
    assert_eq!(l1.concat(l2, &mut live), target);
}

#[test]
fn take_test1() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let nil = Nil::<Level>.alloc(&mut live);
    let take_nil_0 = nil.take(0, &mut live);
    assert_eq!(nil, take_nil_0);
    let take_nil_many = nil.take(999, &mut live);
    assert_eq!(nil, take_nil_many);

    let l1 = param!(["a", "b", "c", "d"], &mut live);
    let take0 = l1.take(0, &mut live);
    let take1 = l1.take(1, &mut live);
    let take2 = l1.take(2, &mut live);
    let take4 = l1.take(4, &mut live);
    let take5 = l1.take(5, &mut live);

    let target0 = nil;
    let target1 = param!(["a"], &mut live);
    let target2 = param!(["a", "b"], &mut live);
    let target4 = param!(["a", "b", "c", "d"], &mut live);
    let target5 = target4;

    assert_eq!(take0, target0);
    assert_eq!(take1, target1);
    assert_eq!(take2, target2);
    assert_eq!(take4, target4);
    assert_eq!(take5, target5);
}


#[test]
fn nodup_test1() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let nil = Nil::<Level>.alloc(&mut live);
    assert!(nil.no_dupes(&mut live).0);

    let l1 = param!(["a", "b", "c", "d"], &mut live);
    assert!(l1.no_dupes(&mut live).0);


    let l6 = param!(["0"], &mut live);
    assert!(l6.no_dupes(&mut live).0);
}

#[test]
#[should_panic]
fn nodup_test2() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let nil = Nil::<Level>.alloc(&mut live);
    assert!(nil.no_dupes(&mut live).0);


    let l2 = param!(["a", "b", "a"], &mut live);
    assert!(!l2.no_dupes(&mut live).0);
}

#[test]
fn len_test0() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let nil = Nil::<Level>.alloc(&mut live);

    let l1 = param!(["a", "b", "c", "d"], &mut live);

    assert_eq!(nil.len(&mut live), 0);
    assert_eq!(l1.len(&mut live), 4);
}

#[test]
fn get_test0() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let nil = Nil::<Level>.alloc(&mut live);

    assert_eq!(nil.get(0, &mut live), None);
    assert_eq!(nil.get(999, &mut live), None);
}

#[test]
fn get_test1() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let l = param!(["a", "b", "c", "d"], &mut live);

    let target0 = Some(param!("a", &mut live));
    let target1 = Some(param!("b", &mut live));
    let target3 = Some(param!("d", &mut live));

    assert_eq!(l.get(0, &mut live), target0);
    assert_eq!(l.get(1, &mut live), target1);
    assert_eq!(l.get(3, &mut live), target3);
    assert_eq!(l.get(4, &mut live), None);
}


#[test]
fn skip_test1() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let l = param!(["a", "b", "c", "d", "e"], &mut live);
    let target = param!(["c", "d", "e"], &mut live);
    let skipped = l.skip(2, &mut live);
    assert_eq!(target, skipped);
}

#[test]
fn skip_test2() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let l = param!(["a", "b", "c", "d", "e"], &mut live);
    let target = param!(["a", "b", "c", "d", "e"], &mut live);
    let skipped = l.skip(0, &mut live);
    assert_eq!(target, skipped);
}


#[test]
fn skip_test3() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();

    let l = param!(["a", "b", "c", "d"], &mut live);
    let target = Nil::<Level>.alloc(&mut live);
    let skipped = l.skip(6, &mut live);
    assert_eq!(target, skipped);
}
