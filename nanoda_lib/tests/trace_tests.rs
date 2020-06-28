#![allow(unused_imports)]
#![allow(unused_variables)]
use nanoda_lib::utils::{ List,  List::*, Env };
use nanoda_lib::name::Name;
use nanoda_lib::level::{ LevelsPtr, Level };
use nanoda_lib::param;
use nanoda_lib::trace::{ NoopTracer, StdoutTracer };

#[test]
fn trace_test0() {
    let mut env = Env::new(StdoutTracer::new());


    let l1 = Nil::<Level>.alloc(&mut env);
    let l2 = param!(["a", "b"], &mut env);
    let target = param!(["a", "b"], &mut env);
    assert_eq!(l1.concat(l2, &mut env).0, target);
}


#[test]
fn trace_test1() {
    let mut env = Env::new(StdoutTracer::new());
    let mut live = env.as_live();


    let l1 = Nil::<Level>.alloc(&mut live);
    let l2 = param!(["a", "b"], &mut live);
    let target = param!(["a", "b"], &mut live);
    assert_eq!(l1.concat(l2, &mut live).0, target);
}

#[test]
fn trace_test2() {
    let mut env = Env::new(NoopTracer);
    let mut live = env.as_live();


    let l1 = Nil::<Level>.alloc(&mut live);
    let l2 = param!(["a", "b"], &mut live);
    let target = param!(["a", "b"], &mut live);
    assert_eq!(l1.concat(l2, &mut live).0, target);

}


#[test]
fn trace_test3() {
    let empty = Vec::<u16>::new();
    let v = vec![0u16, 1u16, 2u16];

}

#[test]
fn trace_test4() {
    let mut env = Env::new(StdoutTracer::new());
    let mut live = env.as_live();

    let l1 = param!("A", &mut live).new_succ(&mut live);
    let l2 = param!("B", &mut live).new_succ(&mut live);

    let target = param!("A", &mut live)
    .new_max(param!("B", &mut live), &mut live)
    .new_succ(&mut live);

    let (combined, _step) = l1.combining(l2, &mut live);
    assert_eq!(target, combined);
}


#[test]
fn subset_nil_nil() {
    let mut env = Env::new(StdoutTracer::new());
    let mut live = env.as_live();

    let nil1 = Nil::<Level>.alloc(&mut live);
    let nil2 = Nil::<Level>.alloc(&mut live);

    let (x, _) = nil1.subset(nil2, &mut live);
    assert!(x);
}

#[test]
fn subset_true() {
    let mut env = Env::new(StdoutTracer::new());
    let mut live = env.as_live();

    let nil = Nil::<Level>.alloc(&mut live);
    let sub = param!(["u", "v"], &mut live);
    let super_1 = param!(["u", "v", "w"], &mut live);
    let super_2 = param!(["v", "v", "w", "u", "u", "w"], &mut live);


    let (b0, _h0) = nil.subset(super_2, &mut live);
    let (b1, _h1) = sub.subset(super_1, &mut live);
    let (b2, _h2) = sub.subset(super_2, &mut live);
    let (b3, _h3) = super_1.subset(super_2, &mut live);
    let (b4, _h4) = super_2.subset(super_1, &mut live);

    assert!(b0);
    assert!(b1);
    assert!(b2);
    assert!(b3);
    assert!(b4);
}


#[test]
fn subset_false() {
    let mut env = Env::new(StdoutTracer::new());
    let mut live = env.as_live();

    let nil = Nil::<Level>.alloc(&mut live);
    let sub1 = param!(["x"], &mut live);

    let super_1 = param!(["u", "v", "w"], &mut live);


    let (b0, _h0) = sub1.subset(nil, &mut live);
    let (b1, _h1) = super_1.subset(sub1, &mut live);
    let (b2, _h2) = sub1.subset(super_1, &mut live);

    assert!(!b0);
    assert!(!b1);
    assert!(!b2);
}
