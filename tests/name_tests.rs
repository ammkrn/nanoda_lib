use nanoda_lib::utils::{ Env, HasNanodaDbg };

use nanoda_lib::name::Name::*;

#[test]
fn name_test0() {
    let mut env = Env::new(false);

    let name = Anon.alloc(&mut env);
    let name = name.new_str(format!("A"), &mut env);
    let name = name.new_str(format!("B"), &mut env);
    let name = name.new_num(999, &mut env);
    let target = name;
    let name = name.new_str(format!("C"), &mut env);

    assert_eq!(name.nanoda_dbg(&env).as_str(), "A.B.999.C");

    let live = env.as_compiler();

    assert_eq!(name.get_prefix(&live), target);
}
