use crate::env::Declar;
use crate::expr::{BinderStyle, Expr::*, FVarId};
use crate::hash64;
use crate::level::Level;
use crate::name::Name;
use crate::util::{get_bool, get_nat, get_string, ExportFile, ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr, TcCtx};
use serde_json::Value as JsonValue;
use std::error::Error;
use std::rc::Rc;
use BinderStyle::*;
use Doc::*;

// Lexical structure was taken from:
// https://github.com/leanprover/lean4/blob/504b6dc93f46785ccddb8c5ff4a8df5be513d887/doc/lexical_structure.md?plain=1#L40
//
// If a name ends up being anonymous in a position that otherwise should require an identifier,
// it's printed as an empty escape sequence `«»`.
//
// If a name uses characters that otherwise should not be valid, it's escaped with double
// french quotes.
const NOT_GREEK: &[char] = &['λ', 'Π', 'Σ'];
const GREEK0: std::ops::Range<char> = 'α'..'ω';
const GREEK1: std::ops::Range<char> = 'Α'..'Ω';
const GREEK2: std::ops::Range<char> = 'ἀ'..'῾';
const COPTIC: std::ops::Range<char> = 'ϊ'..'ϻ';
const LETTERLIKE_SYMBOL: std::ops::Range<char> = '℀'..'\u{214f}';
const SUBSCRIPT0: std::ops::Range<char> = '₀'..'₉';
const SUBSCRIPT1: std::ops::Range<char> = 'ₐ'..'ₜ';
const SUBSCRIPT2: std::ops::Range<char> = 'ᵢ'..'ᵪ';

fn is_letterlike_start(c: char) -> bool {
    c.is_ascii_alphabetic()
        || c == '_'
        || (!NOT_GREEK.contains(&c)) && (GREEK0.contains(&c) || GREEK1.contains(&c) || GREEK2.contains(&c))
        || COPTIC.contains(&c)
        || LETTERLIKE_SYMBOL.contains(&c)
}

fn is_letterlike_rest(c: char) -> bool {
    is_letterlike_start(c)
        || c.is_ascii_digit()
        || c == '!'
        || c == '?'
        || c == '\''
        || SUBSCRIPT0.contains(&c)
        || SUBSCRIPT1.contains(&c)
        || SUBSCRIPT2.contains(&c)
}

fn partition_slice<T>(s: &[T], f: impl Fn(&T) -> bool) -> (&[T], &[T]) {
    let idx = s.partition_point(f);
    (&s[0..idx], &s[idx..])
}

#[derive(Clone)]
enum Doc {
    Text(Rc<str>),
    Concat(DocPtr, DocPtr),
    Line(&'static str),
    Nest(usize, DocPtr),
    Group(DocPtr),
}

impl std::convert::AsRef<Doc> for DocPtr {
    fn as_ref(&self) -> &Doc { self.0.as_ref() }
}

impl From<Doc> for DocPtr {
    fn from(d: Doc) -> DocPtr { DocPtr(Rc::new(d)) }
}

impl From<&str> for DocPtr {
    fn from(s: &str) -> DocPtr { DocPtr(Rc::new(Doc::Text(Rc::from(s)))) }
}

impl From<String> for DocPtr {
    fn from(s: String) -> DocPtr { DocPtr(Rc::new(Doc::Text(Rc::from(s)))) }
}

#[derive(Clone)]
struct DocPtr(Rc<Doc>);

pub const MAX_LEVEL: usize = 1024;

fn line() -> DocPtr { Line(" ").into() }

fn zero_width_line() -> DocPtr { Line("").into() }

impl DocPtr {
    /// Create a `Parenable` that cannot be parenthesized
    fn as_unparenable(&self) -> Parenable { self.as_parenable(MAX_LEVEL) }

    fn as_parenable(&self, inner_level: usize) -> Parenable { Parenable { doc: self.clone(), inner_level } }

    fn concat(&self, r: impl Into<Self>) -> Self { Doc::Concat(self.clone(), r.into()).into() }

    fn mk_nest(&self, idx: usize) -> Self { Nest(idx, self.clone()).into() }

    fn nest_group(&self, idx: usize) -> Self { self.group().mk_nest(idx) }

    fn concat_line(&self, other: impl Into<Self>) -> Self { self.concat(line()).concat(other) }

    fn concat_w_space(self, rhs: impl Into<Self>) -> Self { self.concat(DocPtr::from(" ")).concat(rhs) }

    fn contains_line(&self) -> bool {
        match self.as_ref() {
            Line(_) => true,
            Concat(a, b) => a.contains_line() || b.contains_line(),
            Nest(_, d) => d.contains_line(),
            Text(_) => false,
            Group(a) => a.contains_line(),
        }
    }

    fn dist_to_first_line(&self) -> usize {
        match self.as_ref() {
            Line(_) => 0,
            Concat(a, b) => a.dist_to_line(b.dist_to_first_line()),
            Nest(_, d) => d.dist_to_first_line(),
            Text(t) => t.len(),
            Group(a) => a.dist_to_first_line(),
        }
    }

    fn dist_to_line(&self, after: usize) -> usize {
        if self.contains_line() {
            self.dist_to_first_line()
        } else {
            self.dist_to_first_line() + after
        }
    }

    fn group(&self) -> Self { Group(self.clone()).into() }

    fn flat_size(&self) -> usize {
        match self.as_ref() {
            Concat(a, b) => a.flat_size() + b.flat_size(),
            Nest(_, d) => d.flat_size(),
            Text(t) => t.len(),
            Line(x) => x.len(),
            Group(a) => a.flat_size(),
        }
    }

    fn render(&self, line_width: usize) -> String {
        let mut acc = String::new();
        let mut eol = acc.len() + line_width;

        self.render_aux(0, false, 0, line_width, &mut eol, &mut acc);
        acc
    }

    fn render_aux(
        &self,
        // `nest` is the number of spaces to insert as indentation when a new line begins.
        // This is only "used" in rendering the `Line` constructor.
        nest: usize,
        // If flatmode is true, either the user has asked the output to be printed with no
        // line breaks, or a `Group` node has determined that the grouped contents will
        // fit on the current line without needing to break.
        flatmode: bool,
        dist_to_next_line: usize,
        // Remains constant throughout rendering; the line width chosen by the user.
        line_width: usize,
        eol: &mut usize,
        acc: &mut String,
    ) {
        match self.as_ref() {
            Concat(a, b) => {
                a.render_aux(nest, flatmode, b.dist_to_line(dist_to_next_line), line_width, eol, acc);
                b.render_aux(nest, flatmode, dist_to_next_line, line_width, eol, acc);
            }
            Nest(idx, a) => a.render_aux(nest + idx, flatmode, dist_to_next_line, line_width, eol, acc),
            Text(t) => acc.push_str(t.as_ref()),
            // `flatmode` is false by default; it's `true` if this node was in a group
            // that was determined to fit on the current line.
            Line(x) =>
            // If we're in flatmode, either by user request, or because we've determined
            // that everything left can fit on this line, then just push the alt text
            // to be used when there's no line break; for example a space instead of a
            // line break.
                if flatmode {
                    acc.push_str(x.as_ref());
                } else {
                    acc.push('\n');
                    // Add the spaces for the indentation.
                    *eol = acc.len() + line_width;
                    for _ in 0..nest {
                        acc.push(' ');
                    }
                },
            Group(a) => a.render_aux(
                nest,
                flatmode || acc.len() + a.flat_size() + dist_to_next_line <= *eol,
                dist_to_next_line,
                line_width,
                eol,
                acc,
            ),
        }
    }
}

#[derive(Clone)]
struct Parenable {
    doc: DocPtr,
    inner_level: usize,
}

impl Parenable {
    fn new(doc: DocPtr, inner_level: usize) -> Self { Self { doc, inner_level } }

    /// Given a `Parenable` which has an inner priority value, and a new `outer_priority` value,
    /// if the `outer_priority` is greater than the inner priority, add parentheses around
    /// the doc, otherwise don't add parentheses.
    ///
    /// The higher a given `Parenable` element's inner priority is, the less likely it is to be
    /// parenthesized.
    ///
    /// The higher an `outer_priority` value is, the more likely this doc is to get parens.
    ///
    /// outer_priority = 0 -> never parenthesize.
    ///
    /// outer_priority = MAX -> always parenthesize, unless inner is max.
    pub fn parens(&self, outer_level: usize) -> DocPtr {
        if outer_level > self.inner_level {
            DocPtr::from("(").concat(self.doc.clone()).concat(")")
        } else {
            self.doc.clone()
        }
    }
}

/// "Tile" a sequence of docs; Example:
/// ```ignore
///   doc0 doc1 doc2 doc3 doc4 doc5 doc6 doc7\n\
///   doc8 doc9 doc10 doc11 doc12 doc13 doc14\n\
///   doc15 doc16 doc17 doc18 doc19"
/// ```
fn tile_docs(mut s: impl Iterator<Item = DocPtr>) -> DocPtr {
    match s.next() {
        None => DocPtr::from(""),
        Some(mut out) => {
            for next in s {
                out = out.concat(line().concat(next).group())
            }
            out
        }
    }
}

#[derive(Clone, Debug)]
pub struct PpOptions {
    pub all: bool,
    pub explicit: bool,
    pub universes: bool,
    pub notation: bool,
    pub proofs: bool,
    pub indent: usize,
    pub width: usize,
    pub declar_sep: String,
}

impl TryFrom<&JsonValue> for PpOptions {
    type Error = Box<dyn std::error::Error>;

    fn try_from(v: &JsonValue) -> Result<Self, Self::Error> {
        Ok(Self {
            all: get_bool("all", v, false)?,
            explicit: get_bool("explicit", v, false)?,
            universes: get_bool("universes", v, false)?,
            notation: get_bool("notation", v, true)?,
            proofs: get_bool("proofs", v, false)?,
            indent: get_nat("indent", v, 2)?,
            width: get_nat("width", v, 100)?,
            declar_sep: get_string("declar_sep", v, String::from("\n\n"))?,
        })
    }
}

impl std::default::Default for PpOptions {
    fn default() -> Self { Self::new_default() }
}

impl PpOptions {
    pub fn new_default() -> Self {
        PpOptions {
            all: false,
            explicit: false,
            universes: false,
            notation: true,
            proofs: false,
            indent: 2usize,
            width: 100usize,
            declar_sep: String::from("\n\n"),
        }
    }

    pub fn all() -> Self {
        PpOptions {
            all: true,
            explicit: true,
            universes: true,
            notation: false,
            proofs: true,
            indent: 2usize,
            width: 100usize,
            declar_sep: String::from("\n\n"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct ParsedBinder<'a> {
    is_pi: bool,
    occurs_in_body: bool,
    is_anon: bool,
    has_macro_scopes: bool,
    local_const: ExprPtr<'a>,
    // Keep the name, style, and type inline so we don't have to read
    // the pointer to get that info.
    binder_name: NamePtr<'a>,
    binder_style: BinderStyle,
    binder_type: ExprPtr<'a>,
}

impl<'a> ParsedBinder<'a> {
    fn is_named_pi(&self) -> bool { self.is_pi && !self.is_arrow() }

    /// Whether a binder can be "factored out" by putting it to the left
    /// of the colon;
    ///```ignore
    ///theorem foo : forall (a b : Nat), a + b = b + a := fun a b => Nat.add_comm a b
    /// -- factoring out to
    ///theorem foo (a b : Nat) : a + b = b + a := Nat.add_comm a b
    ///```
    fn can_factor_out(&self) -> bool {
        self.is_pi
        && !self.is_anon
        //&& !self.has_macro_scopes 
        && matches!(self.binder_style, BinderStyle::Default)
    }

    fn is_arrow(&self) -> bool {
        //self.is_pi && matches!(self.binder_style, Default) && (!self.occurs_in_body || self.is_anon)
        self.is_pi
            && matches!(self.binder_style, Default)
            && (!self.occurs_in_body || self.is_anon || self.has_macro_scopes)
    }

    fn is_lambda(&self) -> bool { !self.is_pi }
}

pub struct PrettyPrinter<'x, 't, 'p> {
    pub(crate) ctx: &'x mut TcCtx<'t, 'p>,
}

use crate::util::PpDestination;
impl<'p> ExportFile<'p> {
    pub fn pp_selected_declars(&self, pp_destination: Option<&mut PpDestination>) -> Vec<Box<dyn std::error::Error>> {
        let mut errs = Vec::new();
        if let Some(pp_destination) = pp_destination {
            self.with_ctx(|ctx| {
                for declar_name in ctx.export_file.config.pp_declars.iter() {
                    let n = ctx.name_from_str(declar_name);
                    if let Some(s) = ctx.with_pp(|pp| pp.pp_declar(n)) {
                        if let Err(e) = pp_destination.write_line(s, self.config.pp_options.declar_sep.as_str()) {
                            errs.push(e)
                        }
                    } else {
                        errs.push(Box::<dyn Error>::from(format!(
                            "declaration {} not found during pretty printing",
                            declar_name
                        )))
                    }
                }
            })
        }
        errs
    }
}

impl<'x, 't, 'p> PrettyPrinter<'x, 't, 'p> {
    pub(crate) fn new(ctx: &'x mut TcCtx<'t, 'p>) -> Self { Self { ctx } }

    pub(crate) fn options(&self) -> &PpOptions { &self.ctx.export_file.config.pp_options }

    /// Returns `true` if this string segment of a name can be displayed
    /// without needing to escape; if the characters are lexically correct,
    /// or if the issue is `_@` which accompanies hygienic names.
    fn ok_str(&self, s: StringPtr<'t>) -> bool {
        let s = self.ctx.read_string(s);
        (s.chars().take(1).all(is_letterlike_start) && s.chars().skip(1).all(is_letterlike_rest)) || s == "_@"
    }

    fn should_be_escaped(&self, n: NamePtr<'t>) -> bool { n == self.ctx.anonymous() || self.should_be_escaped_aux(n) }

    fn should_be_escaped_aux(&self, n: NamePtr<'t>) -> bool {
        match self.ctx.read_name(n) {
            Name::Anon => false,
            Name::Str(pfx, sfx, _) => !self.ok_str(sfx) || self.should_be_escaped_aux(pfx),
            Name::Num(pfx, ..) => self.should_be_escaped_aux(pfx),
        }
    }

    fn mk_parsed_binder(
        &self,
        is_pi: bool,
        occurs_in_body: bool,
        is_anon: bool,
        local_const: ExprPtr<'t>,
    ) -> ParsedBinder<'t> {
        if let Local { binder_name, binder_style, binder_type, .. } = self.ctx.read_expr(local_const) {
            let has_macro_scopes = self.ctx.has_macro_scopes(binder_name);
            ParsedBinder {
                is_pi,
                occurs_in_body,
                is_anon,
                has_macro_scopes,
                binder_name,
                binder_style,
                binder_type,
                local_const,
            }
        } else {
            panic!()
        }
    }

    fn pp_bare_binder(&mut self, binder_name: NamePtr<'t>, binder_type: ExprPtr<'t>) -> DocPtr {
        let ty = self.pp_expr_aux(binder_type).parens(1).group();
        self.pp_name_safe(binder_name).concat_w_space(":").concat_line(ty)
    }

    fn telescope(&mut self, binders: &[ParsedBinder<'t>]) -> Vec<DocPtr> {
        let mut acc = Vec::new();
        self.telescope_aux(binders, &mut acc);
        acc
    }

    fn telescope_aux(&mut self, binders: &[ParsedBinder<'t>], acc: &mut Vec<DocPtr>) {
        let (hd, _) = match binders.split_first() {
            Some((hd, tl)) => (hd, tl),
            None => return,
        };

        let (group, rest) = if hd.binder_style == BinderStyle::InstanceImplicit {
            binders.split_at(1)
        } else {
            let closure = |b: &ParsedBinder| b.binder_style == hd.binder_style && b.binder_type == hd.binder_type;
            partition_slice(binders, closure)
        };

        let mapped_group = group.iter().map(|b| match b.is_anon && !b.occurs_in_body {
            true => DocPtr::from("_"),
            false => self.pp_name_safe(b.binder_name),
        });

        let bare =
            tile_docs(mapped_group).concat_w_space(":").concat_line(self.pp_expr_aux(hd.binder_type).parens(1).group());

        let match_result = match hd.binder_style {
            BinderStyle::Default => DocPtr::from("(").concat(bare).concat(")"),
            BinderStyle::Implicit => DocPtr::from("{").concat(bare).concat("}"),
            BinderStyle::StrictImplicit => DocPtr::from("{{").concat(bare).concat("}}"),
            BinderStyle::InstanceImplicit => DocPtr::from("[").concat(bare).concat("]"),
        };

        acc.push(match_result.nest_group(self.options().indent));
        self.telescope_aux(rest, acc);
    }

    fn pp_binders(&mut self, binders: &[ParsedBinder<'t>], inner: Parenable) -> Parenable {
        if let Some((hd, tl)) = binders.split_first() {
            if hd.is_arrow() {
                let tl = self.pp_binders(tl, inner).parens(24);
                self.pp_expr_aux(hd.binder_type)
                    .parens(25)
                    .nest_group(self.options().indent)
                    .concat_w_space("→")
                    .concat(line())
                    .group()
                    .concat(tl)
                    .as_parenable(24)
            } else if hd.is_named_pi() {
                let (group, rest) = partition_slice(binders, |x| x.is_named_pi());
                let telescoped = tile_docs(self.telescope(group).into_iter());
                DocPtr::from("forall")
                    .concat_w_space(telescoped)
                    .concat(",")
                    .nest_group(self.options().indent)
                    .concat_line(self.pp_binders(rest, inner).parens(0))
                    .as_parenable(0)
            } else {
                assert!(hd.is_lambda());
                let (group, rest) = partition_slice(binders, |x| x.is_lambda());
                let telescoped = tile_docs(self.telescope(group).into_iter());
                DocPtr::from("fun")
                    .concat_w_space(telescoped)
                    .concat_w_space("=>")
                    .nest_group(self.options().indent)
                    .concat_line(self.pp_binders(rest, inner).parens(0))
                    .as_parenable(0)
            }
        } else {
            inner
        }
    }

    /// Removes and returns all elements of the leading telescope, whether they're
    /// lambda, pi, or both, also returning the instantiated body.
    ///
    /// The parsed binder elements are free variables with the binder types, and
    /// they carry information about whether they're a pi or lambda, if they're seen
    /// later, etc.
    fn parse_binders(&mut self, mut e: ExprPtr<'t>) -> (Vec<ParsedBinder<'t>>, ExprPtr<'t>) {
        let (mut binders, mut binder_tys) = (Vec::<ParsedBinder>::new(), Vec::new());
        while let Pi { binder_name, binder_style, binder_type, body, .. }
        | Lambda { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(e)
        {
            let binder_type = self.ctx.inst(binder_type, binder_tys.as_slice());
            let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
            let is_pi = matches!(self.ctx.read_expr(e), Pi { .. });
            let is_anon = self.ctx.read_name(binder_name) == Name::Anon;
            let has_var = self.ctx.has_var(body, 0);
            let new_parsed_binder = self.mk_parsed_binder(is_pi, has_var, is_anon, local);
            binders.push(new_parsed_binder);
            binder_tys.push(local);
            e = body;
        }
        let instd = self.ctx.inst(e, binder_tys.as_slice());
        (binders, instd)
    }

    /// `safe` in the sense that the name will be escaped if it doesn't follow the
    /// usual convention for identifiers.
    fn pp_name_safe(&self, n: NamePtr<'t>) -> DocPtr {
        let doc = self.name_to_string(n).as_str().into();
        if self.should_be_escaped(n) {
            DocPtr::from("«").concat(doc).concat(DocPtr::from("»"))
        } else {
            doc
        }
    }

    /// Create a string from a name `n`, leaving the dot-separator in the output string.\
    ///
    /// Example: name_to_string(`Foo.Bar.Baz`) == "Foo.Bar.Baz"
    fn name_to_string(&self, n: NamePtr<'t>) -> String {
        match self.ctx.read_name(n) {
            Name::Anon => String::new(),
            Name::Str(pfx, sfx, _) => {
                let mut out = self.name_to_string(pfx);
                if !out.is_empty() {
                    out.push('.');
                }
                out.push_str(self.ctx.read_string(sfx).as_ref());
                out
            }
            Name::Num(pfx, sfx, _) => {
                let mut out = self.name_to_string(pfx);
                if !out.is_empty() {
                    out.push('.');
                }
                out.push_str(format!("{}", sfx).as_str());
                out
            }
        }
    }

    fn pp_level(&self, lvl: LevelPtr<'t>) -> Parenable {
        use Level::*;
        match self.ctx.read_level(lvl) {
            Param(p, _) => self.pp_name_safe(p).as_unparenable(),
            Max(a, b, _) => DocPtr::from("max")
                .concat_w_space(self.pp_level(a).parens(1))
                .concat_line(self.pp_level(b).parens(1))
                .as_parenable(0),
            IMax(a, b, _) => DocPtr::from("imax")
                .concat_w_space(self.pp_level(a).parens(1))
                .concat_line(self.pp_level(b).parens(1))
                .as_parenable(0),
            _ => {
                let (inner, n) = self.ctx.level_succs(lvl);
                match self.ctx.read_level(inner) {
                    Zero => DocPtr::from(n.to_string()).as_unparenable(),
                    _ => self.pp_level(inner).parens(1).concat("+").concat(n.to_string()).as_parenable(0),
                }
            }
        }
    }

    fn pp_levels(&self, lvls: &[LevelPtr<'t>]) -> DocPtr {
        let as_docs = lvls.iter().copied().map(|lvl| self.pp_level(lvl).parens(0));
        DocPtr::from("{").concat(tile_docs(as_docs)).concat("}").group()
    }

    /// Does this expression infer as a `Pi` with any binder style other than `Default`
    fn is_implicit_fun(&mut self, fun: ExprPtr<'t>) -> bool {
        self.ctx.with_tc(|tc| {
            let ty = tc.whnf_after_infer(fun, crate::tc::InferFlag::InferOnly);
            match tc.ctx.read_expr(ty) {
                Pi { binder_style, .. } => binder_style != BinderStyle::Default,
                _ => false,
            }
        })
    }

    fn pp_fun_app(&mut self, f: ExprPtr<'t>, apps: &Vec<ExprPtr<'t>>) -> Parenable {
        let mut docs = vec![self.pp_expr_aux(f).parens(MAX_LEVEL - 1).group()];
        for arg in apps {
            docs.push(self.pp_expr_aux(*arg).parens(MAX_LEVEL).group());
        }
        Parenable::new(tile_docs(docs.iter().cloned()).nest_group(self.options().indent), MAX_LEVEL - 1)
    }

    fn unfold_apps_pp(&mut self, e: ExprPtr<'t>) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>) {
        match self.ctx.read_expr(e) {
            App { fun, arg, .. } => {
                let (f, mut out) = self.unfold_apps_pp(fun);
                if !(self.is_implicit_fun(fun) && !self.options().explicit) {
                    out.push(arg);
                }
                (f, out)
            }
            _ => (e, Vec::new()),
        }
    }

    fn pp_app(&mut self, e: ExprPtr<'t>) -> Parenable {
        use crate::env::Notation::*;
        let (f, args) = self.unfold_apps_pp(e);
        match self.ctx.read_expr(f) {
            _ if args.is_empty() => self.pp_expr_aux(f),
            Const { name, .. } if self.options().notation => match self.ctx.export_file.notations.get(&name).cloned() {
                Some(Prefix { priority, oper, .. }) if args.len() == 1 => DocPtr::from(oper.as_ref())
                    .concat(zero_width_line())
                    .group()
                    .concat(self.pp_expr_aux(args[args.len() - 1]).parens(priority))
                    .as_parenable(priority - 1),
                Some(Postfix { priority, oper, .. }) if args.len() == 1 => self
                    .pp_expr_aux(args[args.len() - 1])
                    .parens(priority)
                    .concat(zero_width_line())
                    .concat(oper.as_ref())
                    .group()
                    .as_parenable(priority - 1),
                Some(Infix { priority, oper, .. }) if args.len() == 2 => {
                    let lhs = self.pp_expr_aux(args[args.len() - 1]).parens(priority);
                    let rhs = self.pp_expr_aux(args[args.len() - 2]).parens(priority);
                    lhs.concat(oper.as_ref())
                        .concat(zero_width_line())
                        .concat(rhs)
                        .nest_group(self.options().indent)
                        .as_parenable(priority - 1)
                }
                _ => self.pp_fun_app(f, &args),
            },
            _ => self.pp_fun_app(f, &args),
        }
    }

    fn pp_sort(&mut self, level: LevelPtr<'t>) -> Parenable {
        let inner = if self.ctx.is_zero(level) && self.options().notation {
            DocPtr::from("Prop")
        } else if let Level::Succ(pred, ..) = self.ctx.read_level(level) {
            DocPtr::from("Type").concat_w_space(self.pp_level(pred).parens(MAX_LEVEL))
        } else {
            DocPtr::from("Sort").concat_w_space(self.pp_level(level).parens(MAX_LEVEL))
        };
        inner.as_unparenable()
    }

    fn pp_const(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> Parenable {
        let name = if self.options().all || self.options().explicit {
            DocPtr::from("@").concat(self.pp_name_safe(name))
        } else {
            self.pp_name_safe(name)
        };
        if self.options().all || self.options().universes {
            name.concat(self.pp_uparams(levels)).as_unparenable()
        } else {
            name.as_unparenable()
        }
    }

    fn pp_declar_info(&mut self, info: crate::env::DeclarInfo<'t>) -> DocPtr {
        self.pp_name_safe(info.name).concat(self.pp_uparams(info.uparams))
    }

    fn pp_let(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> Parenable {
        let suggestion = self.ctx.mk_unique(binder_name, BinderStyle::Default, binder_type);
        let fresh_lc_name = binder_name;
        let swapped_lc = self.ctx.swap_local_binding_name(suggestion, fresh_lc_name);
        let (n, t) = match self.ctx.read_expr(swapped_lc) {
            Local { binder_name, binder_type, .. } => (binder_name, binder_type),
            _ => panic!(),
        };

        let instd = self.ctx.inst(body, &[swapped_lc]);
        let binder = self.pp_bare_binder(n, t).group();
        let val = self.pp_expr_aux(val).parens(0).group();
        let body = self.pp_expr_aux(instd).parens(0);
        DocPtr::from("let")
            .concat_w_space(binder)
            .concat_w_space(":=")
            .concat_line(val)
            .concat(";")
            .nest_group(self.options().indent)
            .concat_line(body)
            .group()
            .as_parenable(0)
    }

    fn pp_expr_aux(&mut self, e: ExprPtr<'t>) -> Parenable {
        if !self.options().proofs && self.ctx.with_tc(|tc| tc.is_proof(e).0) {
            DocPtr::from("_").as_unparenable()
        } else {
            match self.ctx.read_expr(e) {
                Var { dbj_idx, .. } => DocPtr::from(dbj_idx.to_string()).as_unparenable(),
                Sort { level, .. } => self.pp_sort(level),
                Const { name, levels, .. } => self.pp_const(name, levels),
                Local { binder_name, .. } => self.pp_name_safe(binder_name).as_unparenable(),
                Lambda { .. } | Pi { .. } => {
                    let (binders, instd) = self.parse_binders(e);
                    let new_inner = self.pp_expr_aux(instd);
                    self.pp_binders(binders.as_slice(), new_inner)
                }
                Let { binder_name, binder_type, val, body, .. } => self.pp_let(binder_name, binder_type, val, body),
                App { .. } => self.pp_app(e),
                Proj { idx, structure, .. } => {
                    // Lean's pretty-printer for structure fields is 1-indexed
                    self.pp_expr_aux(structure)
                        .parens(MAX_LEVEL - 1)
                        .group()
                        .concat(DocPtr::from("."))
                        .concat(DocPtr::from((idx + 1).to_string()))
                        .as_unparenable()
                }
                NatLit { ptr, .. } => DocPtr::from(self.ctx.read_bignum(ptr).to_string()).as_unparenable(),
                StringLit { ptr, .. } => DocPtr::from(self.ctx.read_string(ptr).as_ref()).as_unparenable(),
            }
        }
    }

    fn pp_uparams(&mut self, levels: LevelsPtr<'t>) -> DocPtr {
        let uparams = self.ctx.read_levels(levels).clone();
        if uparams.is_empty() {
            DocPtr::from("")
        } else {
            DocPtr::from(".").concat(self.pp_levels(uparams.as_ref()))
        }
    }

    /// Pretty print theorems, definitions, and opaques.
    fn main_def(&mut self, declar: &Declar<'t>, mut val: ExprPtr<'t>) -> DocPtr {
        let (binders, ty) = self.parse_binders(declar.info().ty);
        // inlined parse_params
        let mut slice_split_idx = 0usize;
        // When a def has a value with a leading lambda that repeats binders also present in the type, like:
        //```ignore
        // example : forall (a b), (a + b) = (b + a) := fun (a b) => add_comm a b
        //```
        // We want to try and truncate the leading lambda, instead printing as
        //```ignore
        // example (a b) : (a + b) = (b + a) := add_comm a b
        //```
        //
        // break the loop when at least one of these three conditions is true :
        // 1. binders from the type are exhausted
        // 2. val is no longer a Lambda
        // 3. The binder we're looking at is no longer a pi
        for elem in binders.iter() {
            match self.ctx.read_expr(val) {
                Lambda { body, .. } if elem.can_factor_out() => {
                    slice_split_idx += 1;
                    val = body;
                }
                _ => break,
            }
        }
        let (named_binders, rest_binders) = binders.split_at(slice_split_idx);
        let named_binder_tys = named_binders.iter().map(|x| x.local_const).collect::<std::vec::Vec<_>>();

        let instd = self.ctx.inst(val, named_binder_tys.as_slice());
        let pp_val = {
            let is_prop = self.ctx.with_tc(|tc| tc.is_proposition(declar.info().ty).0);
            line()
                .concat(if is_prop && !self.options().proofs {
                    DocPtr::from("_")
                } else {
                    self.pp_expr_aux(instd).parens(0).group()
                })
                .mk_nest(self.options().indent)
        };

        let telescope = self.telescope(named_binders);
        let tydoc = self.pp_expr_aux(ty);
        let bindersdoc =
            line().concat(self.pp_binders(rest_binders, tydoc).parens(0).group()).mk_nest(self.options().indent);

        let binders = if telescope.is_empty() {
            DocPtr::from(":").concat(bindersdoc).concat_w_space(":=")
        } else {
            tile_docs(telescope.into_iter())
                .nest_group(self.options().indent)
                .concat_w_space(":")
                .concat(bindersdoc)
                .concat_w_space(":=")
                .group()
        };

        DocPtr::from(match declar {
            Declar::Theorem { .. } => "theorem",
            Declar::Definition { .. } => "def",
            Declar::Opaque { .. } => "opaque",
            _ => panic!(),
        })
        .concat_w_space(self.pp_declar_info(*declar.info()))
        .concat_w_space(binders)
        .concat(pp_val)
    }

    /// Pretty print axioms, inductive types, constructors, recursors, and the quotient primitives.
    fn main_axiom(&mut self, declar: &Declar<'t>) -> DocPtr {
        let (binders, instd) = self.parse_binders(declar.info().ty);
        let (named_foralls, rest_binders) = partition_slice(binders.as_slice(), |x| x.is_named_pi());
        let telescope = self.telescope(named_foralls);
        let instd_body = self.pp_expr_aux(instd);
        let binder_ctx = if telescope.is_empty() {
            DocPtr::from(":")
                .concat_line(self.pp_binders(rest_binders, instd_body).parens(0).group())
                .nest_group(self.options().indent)
        } else {
            tile_docs(telescope.into_iter())
                .concat_w_space(":")
                .concat_line(self.pp_binders(rest_binders, instd_body).parens(0).group())
                .nest_group(self.options().indent)
        };

        DocPtr::from(match declar {
            Declar::Axiom { .. } => "axiom",
            Declar::Quot { .. } => "Quotient primitive",
            Declar::Inductive { .. } => "inductive",
            Declar::Constructor { .. } => "constructor",
            Declar::Recursor { .. } => "recursor",
            _ => panic!(),
        })
        .concat_w_space(self.pp_declar_info(*declar.info()))
        .concat_w_space(binder_ctx)
    }

    /// Pretty print a declaration by name. Returns `None` if this declaration
    /// does not exist in this environment.
    pub fn pp_declar(&mut self, declar_name: NamePtr<'t>) -> Option<String> {
        self.ctx.export_file.declars.get(&declar_name).cloned().map(|declar| {
            let doc = match declar {
                Declar::Definition { val, .. } | Declar::Theorem { val, .. } | Declar::Opaque { val, .. } =>
                    self.main_def(&declar, val),
                _ => self.main_axiom(&declar),
            };
            doc.group().render(self.options().width)
        })
    }

    /// Pretty print an expression. If this is  part of a larger declaration, use `pp_declar`
    pub fn pp_expr(&mut self, e: ExprPtr<'t>) -> String {
        self.pp_expr_aux(e).parens(0).group().render(self.options().width)
    }
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Does `e` contain a bound variable with deBruijn index `i`.
    fn has_var(&self, e: ExprPtr<'t>, i: u16) -> bool {
        if self.num_loose_bvars(e) <= i {
            return false
        }
        match self.read_expr(e) {
            Var { dbj_idx, .. } => dbj_idx == i,
            App { fun: a, arg: b, .. } => self.has_var(a, i) || self.has_var(b, i),
            Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } =>
                self.has_var(binder_type, i) || self.has_var(body, i + 1),
            Let { binder_type, val, body, .. } =>
                self.has_var(binder_type, i) || self.has_var(val, i) || self.has_var(body, i + 1),
            Proj { structure, .. } => self.has_var(structure, i),
            Sort { .. } | Const { .. } | NatLit { .. } | StringLit { .. } => false,
            Local { .. } => panic!(),
        }
    }

    fn swap_local_binding_name(&mut self, e: ExprPtr<'t>, new_name: NamePtr<'t>) -> ExprPtr<'t> {
        match self.read_expr(e) {
            Local { binder_style, binder_type, id: id @ FVarId::Unique(_), .. } => {
                let hash = hash64!(crate::expr::LOCAL_HASH, new_name, binder_style, binder_type, id);
                self.alloc_expr(Local { binder_name: new_name, binder_style, binder_type, id, hash })
            }
            _ => panic!(),
        }
    }

    /// Parse a dot-separated string as a `Name`. For any given name segment, if it parses
    /// as a u64, it will be treated as coming form the `Num` constructor, otherwise the
    /// `Str` constructor.
    #[allow(dead_code)]
    pub(crate) fn name_from_str(&mut self, s: &str) -> NamePtr<'t> {
        let mut out = self.anonymous();
        for segment in s.split('.') {
            if let Ok(n) = segment.parse::<u64>() {
                out = self.num(out, n)
            } else {
                let sfx = self.alloc_string(std::borrow::Cow::Owned(segment.to_string()));
                out = self.str(out, sfx);
            }
        }
        out
    }

    #[allow(dead_code)]
    pub(crate) fn has_macro_scopes(&self, n: NamePtr<'t>) -> bool {
        match self.read_name(n) {
            Name::Anon => false,
            Name::Str(_, sfx, _) => self.read_string(sfx) == "_hyg",
            Name::Num(pfx, ..) => self.has_macro_scopes(pfx),
        }
    }
}
