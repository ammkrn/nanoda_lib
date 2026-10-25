use crate::name::{format_name, is_id_first, is_id_rest, parse_name, NameComponent};
use crate::parser::parse_export_file;
use crate::pretty_printer::PpOptions;
use crate::tests::util::test_ctx;
use crate::util::{Config, PpDestination};
use std::borrow::Cow;
use std::error::Error;
use std::fs::File;
use std::io::{BufWriter, Cursor};

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

#[test]
fn identifier_characters() {
    // Both ends of each of Lean's ranges, and the characters just outside them.
    let first =
        ['a', 'z', 'A', 'Z', '_', 'α', 'ω', 'Α', 'Ω', 'ϊ', 'ϻ', 'ἀ', '῾', '℀', '⅏', '𝒜', '𝖟', 'À', 'ÿ', 'Ā', 'ſ'];
    let rest = ['0', '9', '\'', '!', '?', '₀', '₉', 'ₐ', 'ₜ', 'ᵢ', 'ᵪ', 'ⱼ'];
    let neither = [
        'λ', 'Π', 'Σ', '×', '÷', 'ΐ', 'Ϊ', 'ΰ', 'ϼ', 'ỿ', '\u{1fff}', '\u{20ff}', '⅐', '𝒛', '𝖠', '¿', 'ƀ', 'ⁿ', '₊',
        '\u{208f}', '\u{209d}', 'ᵡ', 'ᵫ', 'ⱻ', 'ⱽ', '.', ' ', '«', '»', '-', '#',
    ];
    for c in first {
        assert!(is_id_first(c) && is_id_rest(c), "{c:?}");
    }
    for c in rest {
        assert!(!is_id_first(c) && is_id_rest(c), "{c:?}");
    }
    for c in neither {
        assert!(!is_id_first(c) && !is_id_rest(c), "{c:?}");
    }
}

fn str_comp(s: &str) -> NameComponent { NameComponent::Str(s.to_string()) }

fn num_comp(n: u64) -> NameComponent { NameComponent::Num(n) }

#[test]
fn parse_name_components() {
    assert_eq!(parse_name("propext"), Some(vec![str_comp("propext")]));
    assert_eq!(parse_name("Quot.sound"), Some(vec![str_comp("Quot"), str_comp("sound")]));
    assert_eq!(parse_name("x'.a_b!.c?"), Some(vec![str_comp("x'"), str_comp("a_b!"), str_comp("c?")]));
    assert_eq!(parse_name("α₁.ω.é"), Some(vec![str_comp("α₁"), str_comp("ω"), str_comp("é")]));
}

#[test]
fn parse_name_escaped_components() {
    assert_eq!(parse_name("«Quot.sound»"), Some(vec![str_comp("Quot.sound")]));
    assert_eq!(parse_name("«».propext"), Some(vec![str_comp(""), str_comp("propext")]));
    assert_eq!(parse_name("A.«b c».d"), Some(vec![str_comp("A"), str_comp("b c"), str_comp("d")]));
    assert_eq!(parse_name("«x»"), Some(vec![str_comp("x")]));
    assert_eq!(parse_name("««a»"), Some(vec![str_comp("«a")]));
}

#[test]
fn parse_name_numeric_components() {
    assert_eq!(parse_name("a.1"), Some(vec![str_comp("a"), num_comp(1)]));
    assert_eq!(parse_name("a.007"), Some(vec![str_comp("a"), num_comp(7)]));
    assert_eq!(parse_name("a.«1»"), Some(vec![str_comp("a"), str_comp("1")]));
    assert_eq!(parse_name("1.a"), Some(vec![num_comp(1), str_comp("a")]));
    assert_eq!(parse_name("a.18446744073709551615"), Some(vec![str_comp("a"), num_comp(u64::MAX)]));
    assert_eq!(parse_name("a.18446744073709551616"), None);
}

#[test]
fn parse_name_rejects_malformed_names() {
    let malformed =
        ["", ".", "a.", ".a", "a..b", "«a", "a.«b", "«a»b", "a b", "a-b", "1a", "λ", "₁", "a.'b", "?u", "[anonymous]"];
    for s in malformed {
        assert_eq!(parse_name(s), None, "input: {s:?}");
    }
}

#[test]
fn format_name_escapes_components() {
    assert_eq!(format_name(&[str_comp("Quot"), str_comp("sound")]), "Quot.sound");
    assert_eq!(format_name(&[str_comp("Quot.sound")]), "«Quot.sound»");
    assert_eq!(format_name(&[str_comp(""), str_comp("propext")]), "«».propext");
    assert_eq!(format_name(&[str_comp("a"), num_comp(1), str_comp("1")]), "a.1.«1»");
    assert_eq!(format_name(&[str_comp("α₁"), str_comp("b c")]), "α₁.«b c»");
    assert_eq!(format_name(&[str_comp("₁"), str_comp("'a"), str_comp("x✝")]), "«₁».«'a».«x✝»");
    assert_eq!(format_name(&[str_comp("a»b")]), "a»b");
    assert_eq!(format_name(&[]), "[anonymous]");
}

#[test]
fn format_name_round_trips() {
    use rand::{rngs::StdRng, RngExt, SeedableRng};

    // Identifier and non-identifier characters, but not `»`, which can't be escaped.
    const CHARS: &[char] = &['a', 'Z', '_', '0', '9', '.', ' ', '«', '\'', '!', '?', 'α', 'λ', '₁', 'é', '×'];
    let mut rng = StdRng::seed_from_u64(0);
    for _ in 0..10_000 {
        let name: Vec<NameComponent> = (0..rng.random_range(1..=4))
            .map(|_| {
                if rng.random_bool(0.2) {
                    NameComponent::Num(rng.random())
                } else {
                    NameComponent::Str(
                        (0..rng.random_range(0..=4)).map(|_| CHARS[rng.random_range(0..CHARS.len())]).collect(),
                    )
                }
            })
            .collect();
        assert_eq!(parse_name(&format_name(&name)), Some(name));
    }
}

#[test]
fn context_names_preserve_quoted_component_boundaries() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        for source in ["A", "«b c»", "A.«b c»", "A.«b.c»"] {
            let components = parse_name(source).unwrap();
            let name = ctx.name_from_components(&components);
            assert_eq!(ctx.name_components(name), components, "input: {source}");
            assert_eq!(format_name(&ctx.name_components(name)), source, "input: {source}");
        }
    })
}

fn quoted_name_config(pp_declars: Vec<String>) -> Config {
    let names = ["A", "«b c»", "A.«b c»", "A.«b.c»"].map(str::to_string).to_vec();
    Config {
        export_file_path: None,
        use_stdin: true,
        permitted_axioms: Some(names),
        unpermitted_axiom_hard_error: true,
        num_threads: 1,
        nat_extension: false,
        string_extension: false,
        pp_declars: Some(pp_declars),
        unknown_pp_declar_hard_error: true,
        pp_options: PpOptions::default(),
        pp_output_path: None,
        pp_to_stdout: false,
        print_success_message: false,
        print_axioms: false,
        unsafe_permit_all_axioms: false,
    }
}

const QUOTED_NAME_EXPORT: &str = concat!(
    "{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"470d5ce1400764999581fd26d5d72b00d990b0f4\",\"version\":\"4.35.0-rc3\"}}}\n",
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
    "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"b c\"}}\n",
    "{\"in\":3,\"str\":{\"pre\":1,\"str\":\"b c\"}}\n",
    "{\"in\":4,\"str\":{\"pre\":1,\"str\":\"b.c\"}}\n",
    "{\"ie\":0,\"sort\":0}\n",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"type\":0}}\n",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":3,\"type\":0}}\n",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":4,\"type\":0}}\n",
);

#[test]
fn pp_declars_select_quoted_names_by_components() {
    let requested = ["A", "«b c»", "A.«b c»", "A.«b.c»"].map(str::to_string).to_vec();
    let (export, _) = parse_export_file(Cursor::new(QUOTED_NAME_EXPORT), quoted_name_config(requested)).unwrap();
    let path = std::env::temp_dir().join(format!("nanoda-quoted-names-{}.txt", std::process::id()));
    let file = File::create(&path).unwrap();
    let mut destination = PpDestination::File(BufWriter::new(file));
    assert!(export.pp_selected_declars(Some(&mut destination)).is_empty());
    drop(destination);
    let output = std::fs::read_to_string(&path).unwrap();
    std::fs::remove_file(path).unwrap();
    for name in ["A", "«b c»", "A.«b c»", "A.«b.c»"] {
        assert!(output.contains(&format!("axiom {name} : Prop")), "missing {name:?} in {output:?}");
    }
}

#[test]
fn pp_declars_reject_flattened_non_identifier_alias() {
    let result = parse_export_file(Cursor::new(QUOTED_NAME_EXPORT), quoted_name_config(vec!["A.b c".to_string()]));
    match result {
        Err(error) => assert_eq!(error.to_string(), "invalid name in pp_declars: \"A.b c\""),
        Ok(_) => panic!("flattened non-identifier alias was accepted"),
    }
}
