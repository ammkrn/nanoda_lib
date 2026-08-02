use crate::tests::util::test_ctx;
use std::error::Error;
use std::borrow::Cow;

#[test]
fn pfx_test_anon() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        assert_eq!(ctx.get_pfx(ctx.anonymous()), ctx.anonymous());
    })
}

#[test]
fn pfx_test_str0() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let aaa = ctx.str1("aaa");
        assert_eq!(ctx.get_pfx(aaa), aaa);
    })
}

#[test]
fn pfx_test_num0() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let anon = ctx.anonymous();
        let n0 = ctx.num(anon, 123);
        assert_eq!(ctx.get_pfx(n0), n0);
    })
}

#[test]
fn pfx_test_str1() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let bbb = ctx.alloc_string(Cow::from("bbb"));
        let ccc = ctx.alloc_string(Cow::from("ccc"));
        let a = ctx.str1("aaa");
        let b = ctx.str(a, bbb);
        let c = ctx.str(b, ccc);
        let d = ctx.num(c, 1234);
        let pfx1 = ctx.get_pfx(d);
        let pfx2 = ctx.get_pfx(pfx1);
        assert_eq!(pfx1, a);
        assert_eq!(pfx2, pfx1);
    })
}


