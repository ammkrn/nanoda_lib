use nanoda_lib::utils::{ List,  List::*, Env };

use nanoda_lib::name::Name;
use nanoda_lib::level::{ LevelsPtr, Level };
use nanoda_lib::param;




#[test]
fn util_test2() {
    let mut env = Env::new(false);
    let mut env = env.as_compiler();

    let l1 = param!(["u", "v"], &mut env);
    let p1 = param!("u", &mut env);
    let r = l1.mem(p1, &env);
    println!("mem result : {}\n", r);
}


#[test]
fn pos_test0() {
    let mut env = Env::new(false);
    let mut live = env.as_compiler();

    let l = param!(["a", "b", "c", "d", "e"], &mut live);

    let param_a = param!("a", &mut live);
    let param_b = param!("b", &mut live);
    let param_c = param!("c", &mut live);
    let param_d = param!("d", &mut live);
    let param_e = param!("e", &mut live);
    let param_z = param!("z", &mut live);

    assert_eq!(l.pos(param_a, &live), Some(0));
    assert_eq!(l.pos(param_b, &live), Some(1));
    assert_eq!(l.pos(param_c, &live), Some(2));
    assert_eq!(l.pos(param_d, &live), Some(3));
    assert_eq!(l.pos(param_e, &live), Some(4));
    assert_eq!(l.pos(param_z, &live), None);
}


#[test]
fn concat_test0() {
    let mut env = Env::new(false);
    let mut live = env.as_compiler();

    let l1 = param!(["a", "b"], &mut live);

    let l2 = param!(["c", "d"], &mut live);

    let target = param!(["a", "b", "c", "d"], &mut live);
    assert_eq!(l1.concat(l2, &mut live), target);
}


#[test]
fn concat_test1() {
    let mut env = Env::new(false);
    let mut live = env.as_compiler();

    let l1 = param!(["a", "b"], &mut live);
    let l2 = Nil::<Level>.alloc(&mut live);
    let target = param!(["a", "b"], &mut live);
    assert_eq!(l1.concat(l2, &mut live), target);

}
#[test]
fn concat_test2() {
    let mut env = Env::new(false);
    let mut live = env.as_compiler();

    let l1 = Nil::<Level>.alloc(&mut live);
    let l2 = param!(["a", "b"], &mut live);
    let target = param!(["a", "b"], &mut live);
    assert_eq!(l1.concat(l2, &mut live), target);
}

