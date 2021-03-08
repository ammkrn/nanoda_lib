use std::sync::atomic::{ AtomicUsize, Ordering::Relaxed };
use std::fs::File;
use std::io::{ BufRead, BufReader };
use std::str::SplitWhitespace;

use crossbeam_utils::thread;

use crate::name::{ NamePtr, Name };
use crate::level::{ LevelPtr, LevelsPtr, Level };
use crate::expr::{ ExprPtr, Expr };
use crate::env::{ DeclarSpec, DeclarSpec::*, Notation };
use crate::inductive::IndBlock;
use crate::utils::{ 
    Env, 
    EnvZst,
    HasMkPtr,
    Ptr,
    alloc_str,
    List::* 
};


pub struct Parser  {
    num_threads : usize,
    buf_reader : BufReader<File>,
    string_buffer : String,
    line_num : usize,
    finished : bool,
    debug_mode: bool,
}

impl Parser {
    pub fn new(num_threads : usize, buf_reader : BufReader<File>, debug_mode: bool) -> Self {
        Parser {
            num_threads,
            buf_reader,
            string_buffer : String::new(),
            line_num : 0usize,
            finished : false,
            debug_mode
        }
    }

    pub fn parser_loop(&mut self) -> usize {
        let mut env = Env::new(self.debug_mode);
        let mut specs = Vec::<DeclarSpec>::new();

        loop {
            self.line_num += 1;

            match self.buf_reader.read_line(&mut self.string_buffer) {
                Err(e) => panic!("Error in handling outer_loop! {}\n", e),
                Ok(0) => { self.finished = true; break }
                Ok(..) => {
                    let mut ws = self.string_buffer.split_whitespace();
                    match ws.next().expect("Failed to read split_whitespace") {
                        | s @ "#PREFIX"
                        | s @ "#INFIX" 
                        | s @ "#POSTFIX" => env.make_notation(s, &mut ws),
                        "#AX" => env.make_axiom(&mut ws, &mut specs),
                        "#DEF" => env.make_definition(&mut ws, &mut specs),
                        "#QUOT" => env.make_quot(&mut specs),
                        "#IND" => env.make_inductive(&mut ws, &mut specs),
                        owise => env.parse_primitive(owise, &mut ws),
                    }
                }
            }
            self.string_buffer.clear();
        }

        assert!(self.finished);
        env.compile_loop(specs);
        env.check_loop(self.num_threads);
        env.declars.len()
    }


}

impl<'e> Env<'e> {
    fn parse_primitive(&mut self, lead : &str, ws : &mut SplitWhitespace) {
        let leading_num = match lead.parse::<usize>() {
            Ok(n) => n,
            Err(e) => panic!("Failed to parse leading num : {}\n", e),
        };

        let mut as_chars = ws.next().expect("as_chars").chars();
        assert!(as_chars.next() == Some('#'));
        
        match as_chars.next() {
           Some('N') => { self.make_name(leading_num, as_chars.next().unwrap(), ws); },
           Some('U') => { self.make_level(leading_num, as_chars.next().unwrap(), ws); },
           Some('E') => { self.make_expr(leading_num, as_chars.next().unwrap(), ws); },
           owise => panic!("Neither Name, nor Universe, nor Expr : {:?} : {:#?}\n", owise, ws)
        }
    }    

    fn get_name(&mut self, ws : &mut SplitWhitespace) -> NamePtr<'e> {
        let lean_pos = parse_usize(ws);
        EnvZst.mk_ptr(lean_pos)
    }    

    fn get_level(&mut self, ws : &mut SplitWhitespace) -> LevelPtr<'e> {
        let lean_pos = parse_usize(ws);
        EnvZst.mk_ptr(lean_pos)
    }    


    fn get_expr(&mut self, ws : &mut SplitWhitespace) -> ExprPtr<'e> {
        let lean_pos = parse_usize(ws);
        EnvZst.mk_ptr(lean_pos)
    }    

    // Given a sequence of numbers [n1, n2, n3], collect the sequence
    // [levels[n1], levels[n2], levels[n3]] into a list.
    fn get_levels(&mut self, ws : &mut SplitWhitespace) -> LevelsPtr<'e> {
        let mut base = Nil::<Level>.alloc(self);
        for char_chunk in ws.rev() {
            let pos = char_chunk.parse::<usize>().expect("uparams_char_chunk");
            base = Cons(EnvZst.mk_ptr(pos), base).alloc(self)
        }
        base
    }

    // Given a sequence of numbers [x1, x2, .., xN], collect the sequence
    // of names [names[x1], names[x2], .., names[xN]], then map over
    // them with the `new_param : Name -> Level` constructor.
    // ** Does not need to be traced since it only manipulates extant items.
    fn get_uparams(&mut self, ws : &mut SplitWhitespace) -> LevelsPtr<'e> {
        let mut base = Nil::<Level>.alloc(self);
        for char_chunk in ws.rev() {
            let pos = char_chunk.parse::<usize>().expect("uparams_char_chunk");
            let fetched : Ptr<Name> = EnvZst.mk_ptr(pos);
            base = Cons(fetched.new_param(self), base).alloc(self)
        };
        base
    }        

    fn make_notation(&mut self, discrim : &str, ws : &mut SplitWhitespace) {
        let name = self.get_name(ws);
        let priority = parse_usize(ws);
        let symbol = alloc_str(ws.collect::<String>(), self);
        let made = match discrim {
            "#PREFIX"  => Notation::new_prefix(name, priority, symbol),
            "#INFIX"   => Notation::new_infix(name, priority, symbol),
            "#POSTFIX" => Notation::new_postfix(name, priority, symbol),
            _ => unreachable!(),
        };

        self.notations.insert(name, made);
    }

    // #[trace(parser_new_name)]
    fn make_name(&mut self, lean_pos : usize, kind : char, ws : &mut SplitWhitespace) -> Ptr<Name> {
        let prefix_name = self.get_name(ws);
        let new_name = match kind {
            'S' => prefix_name.new_str(parse_rest_string(ws), self),
            'I' => prefix_name.new_num(parse_u64(ws), self),
            owise => unreachable!("parser::make_name, {}\n", owise)
        };

        match new_name {
            Ptr::E(index, ..) => assert_eq!(index as usize, lean_pos),
            _ => unreachable!()
        }

        new_name
    }

    // #[trace(parser_new_level)]
    fn make_level(&mut self, lean_pos : usize, kind : char, ws : &mut SplitWhitespace) -> Ptr<Level> {
         let new_level = match kind {
             'S' => self.get_level(ws).new_succ(self),
             'M' => self.get_level(ws).new_max(self.get_level(ws), self),
             'I' => self.get_level(ws).new_imax(self.get_level(ws), self),
             'P' => self.get_name(ws).new_param(self),
             owise => unreachable!("parser::make_level. owise : {:#?}\n", owise)
         };

        match new_level {
            Ptr::E(index, ..) => assert_eq!(index as usize, lean_pos),
            _ => unreachable!()
        }

        new_level
    }    

    // #[trace(parser_new_expr)]
    fn make_expr(&mut self, lean_pos : usize, kind : char, ws : &mut SplitWhitespace) -> Ptr<Expr> {
        let new_expr = match kind {
            'V' => <Ptr<Expr>>::new_var(parse_u16(ws), self),
            'S' => self.get_level(ws).new_sort(self),
            'C' => <Ptr<Expr>>::new_const(self.get_name(ws), self.get_levels(ws), self),
            'A' => self.get_expr(ws).new_app(self.get_expr(ws), self),
            'P' => {
                let b_style = parse_binder_info(ws);
                let b_name = self.get_name(ws);
                let b_type = self.get_expr(ws);
                let body   = self.get_expr(ws);
                <Ptr<Expr>>::new_pi(b_name, b_type, b_style, body, self)
            }
            'L' => {
                let b_style = parse_binder_info(ws);
                let b_name = self.get_name(ws);
                let b_type = self.get_expr(ws);
                let body   = self.get_expr(ws);
                <Ptr<Expr>>::new_lambda(b_name, b_type, b_style, body, self)
            }
            'Z' => {

                let b_name = self.get_name(ws);
                let b_type = self.get_expr(ws);
                let val    = self.get_expr(ws);
                let body   = self.get_expr(ws);
                <Ptr<Expr>>::new_let(b_name, b_type, crate::expr::BinderStyle::Default, val, body, self)
            }
            otherwise => unreachable!("parser `make_expr` line : {} expectex expression cue, got {:?}", line!(), otherwise)
        };

        match new_expr {
            Ptr::E(index, ..) => assert_eq!(index as usize, lean_pos),
            _ => unreachable!()
        }

        new_expr
    }    

    fn make_axiom(&mut self, ws : &mut SplitWhitespace, specs : &mut Vec<DeclarSpec<'e>>) {
        let name = self.get_name(ws);
        let type_ = self.get_expr(ws);
        let uparams = self.get_uparams(ws);        
        let axiom = DeclarSpec::new_axiom(
            name, 
            uparams,
            type_,
            false
        );
        specs.push(axiom);
    }

    fn make_definition(&mut self, ws : &mut SplitWhitespace, specs : &mut Vec<DeclarSpec<'e>>) {
        let name = self.get_name(ws);
        let type_ = self.get_expr(ws);
        let val = self.get_expr(ws);        
        let uparams = self.get_uparams(ws);
        let definition = DeclarSpec::new_def(
            name,
            uparams,
            type_,
            val,
            false
        );
        specs.push(definition);
    }


    fn make_quot(&mut self, specs : &mut Vec<DeclarSpec>) {
        specs.push(DeclarSpec::new_quot());
    }

    fn make_inductive(&mut self, ws : &mut SplitWhitespace, specs : &mut Vec<DeclarSpec<'e>>) {
        let num_params = parse_u16(ws);
        let name       = self.get_name(ws);
        let type_      = self.get_expr(ws);

        let num_intros = parse_u16(ws);
        let rest_usize = parse_rest_usize(ws);
        let (cnstr_indices, uparam_indices) = rest_usize.split_at(2 * (num_intros as usize));

        let mut uparams = Nil::<Level>.alloc(self);
        for index in uparam_indices.into_iter().rev() {
            let param = EnvZst.mk_ptr(*index).new_param(self);
            uparams = Cons(param, uparams).alloc(self);
        }

        // This is technically a change in direction for all of these sequences.
        // (ind type and ind name only have one element for lean3 though)
        // We read them as [c0, c1, .., cN]
        // but we place them in the list as [cN, .., c1, c0]
        // We end up needing this to make things nicer in inductive.
        //let /*mut*/ ind_names = list!([name], self);
        //let /*mut*/ ind_types = list!([type_], self);
        let ind_names = Cons(name, Nil::<Name>.alloc(self)).alloc(self);
        let ind_types = Cons(type_, Nil::<Expr>.alloc(self)).alloc(self);
        let mut cnstr_names = Nil::<Name>.alloc(self);
        let mut cnstr_types = Nil::<Expr>.alloc(self);
        let mut num_cnstrs = 0u16;

        // When we actually have the possibility of mutuals, this will
        // be in another loop that's like `for i in num_inductives`
        // which creates separate lists for each batch of constructors
        for two_slice in cnstr_indices.chunks(2usize).rev() {
            let cnstr_name = EnvZst.mk_ptr(two_slice[0]);
            let cnstr_type = EnvZst.mk_ptr(two_slice[1]);
            num_cnstrs += 1;

            cnstr_names = Cons(cnstr_name, cnstr_names).alloc(self);
            cnstr_types = Cons(cnstr_type, cnstr_types).alloc(self);
        }

        let indblock = IndBlock::new(
            num_params, 
            uparams,
            ind_names, 
            ind_types, 
            vec![num_cnstrs],
            cnstr_names, 
            cnstr_types, 
            false,
            self
        );

        specs.push(InductiveSpec(indblock))
    }            

    pub fn compile_loop(&mut self, specs : Vec<DeclarSpec<'e>>) {
        for spec in specs {
            spec.compile(&mut self.as_compiler());
        }
    }

    pub fn check_loop(&self, num_threads : usize) {
        if num_threads == 0 || num_threads == 1 {
            let mut task_idx = 0usize;
            loop {
                match self.declars.get_index(task_idx) {
                    None => break,
                    Some((_, d)) => {
                        task_idx += 1;
                        let mut checker = self.as_checker();
                        d.check(true, &mut checker);
                    }
                }
            }
        } else {
            let next = AtomicUsize::new(0);
            thread::scope(|s| {
                let mut threads = Vec::new();
                for _ in 0..num_threads {
                    let t = s
                    .builder()
                    .stack_size(8388608)
                    .spawn(|_| {
                        loop {
                            let task_idx = next.fetch_add(1, Relaxed);
                            match self.declars.get_index(task_idx) {
                                None => break,
                                Some((_, d)) => {
                                    let mut checker = self.as_checker();
                                    d.check(true, &mut checker);
                                }
                            }

                        }
                    }).expect("failed to successfully spawn a scoped thread in `check_loop`");
                    threads.push(t);
                }
                for t in threads {
                    t.join().expect("A thread in `check_loop` panicked while being joined");
                }
            }).expect("failed to unwrap thread scope successfully");
        }

        println!("Successfully checked {} declarations!", self.declars.len());
    }
}

fn parse_usize(ws : &mut SplitWhitespace) -> usize {
    ws.next()
      .expect("parser::parse_usize::next()")
      .parse::<usize>()
      .expect("parser::parse_usize::and_then")
}

fn parse_u64(ws : &mut SplitWhitespace) -> u64 {
    ws.next()
      .expect("parser::parse_u64::next()")
      .parse::<u64>()
      .expect("parser::parse_u64::and_then")
}

fn parse_u16(ws : &mut SplitWhitespace) -> u16 {
    ws.next()
      .expect("parser::parse_u16::next")
      .parse::<u16>()
      .expect("parser::parse_u16::parse")
}
  
  
fn parse_rest_usize(ws : &mut SplitWhitespace) -> Vec<usize> {
    let mut sink = Vec::new();
    for char_chunk in ws {
        let parsed = char_chunk.parse::<usize>().expect("rest_usize::loop");
        sink.push(parsed)
    }
    sink
}
  
fn parse_rest_string(ws : &mut SplitWhitespace) -> String {
  ws.collect::<String>()
}

fn parse_binder_info(ws : &mut SplitWhitespace) -> crate::expr::BinderStyle {
  ws.next().map(|elem| match elem {
      s if s.contains("#BD") => crate::expr::BinderStyle::Default,
      s if s.contains("#BI") => crate::expr::BinderStyle::Implicit,
      s if s.contains("#BC") => crate::expr::BinderStyle::InstImplicit,
      s if s.contains("#BS") => crate::expr::BinderStyle::StrictImplicit,
      _ => unreachable!(),
  }).expect("parse_binder_info")
}
