#![allow(unused_imports)]
#![allow(unused_variables)]
use nanoda_lib::utils::{ alloc_str, Ptr, ListPtr, IsCtx, IsLiveCtx, Store, Env, Live, EnvZst, LiveZst, HasMkPtr, Set, HasNanodaDbg };
use nanoda_lib::name::{ NamePtr, Name::* };
use nanoda_lib::level::{ LevelPtr, Level::* };

#[test]
fn name_test0() {
    let mut env = Env::new(());

    let name = Anon.alloc(&mut env);
    let name = name.new_str(format!("A"), &mut env);
    let name = name.new_str(format!("B"), &mut env);
    let name = name.new_num(999, &mut env);
    let target = name;
    let name = name.new_str(format!("C"), &mut env);

    assert_eq!(name.nanoda_dbg(&env).as_str(), "A.B.999.C");

    let mut live = env.as_live();

    assert_eq!(name.get_prefix(&mut live).0, target);
}


/*
This should not compile.

#[test]
fn name_testX() {
    let mut env = Env::new(());

    let name = Anon.alloc(&mut env);
    let name = name.new_str(format!("A"), &mut env);
    let name = name.new_str(format!("B"), &mut env);

    let live_name;
    {
        let mut live = env.as_live();
        let name = name.new_num(999, &mut live);
        let name = name.new_str(format!("C"), &mut live);
        live_name = name;
    }

    let _x = live_name.nanoda_dbg(&env);
}
*/

#[test]
fn name_test1() {
    let mut env = Env::new(());

    let s = alloc_str(format!("ASTRING"), &mut env);

    let name = Anon.alloc(&mut env);
    let name = name.new_str(format!("A"), &mut env);
    let name = name.new_str(format!("B"), &mut env);

    let live_name;
    {
        let mut live = env.as_live();
        let name = name.new_num(999, &mut live);
        let name = name.new_str(format!("C"), &mut live);
        let name = name.new_num(1, &mut live);
        let test_s = alloc_str(format!("ASTRING"), &mut live);
        assert_eq!(s, test_s);
        live_name = name.insert_env(&mut live.env, &live.store);
    }

    assert!(live_name.in_env());
    assert_eq!(live_name.nanoda_dbg(&env).as_str(), "A.B.999.C.1");
    //println!("raw : {:#?}\n", live_name);
    //println!("raw inner : {:#?}\n", live_name.read(&env));

}