use crate::level::{ LevelPtr, Level::* };
use crate::utils::{ 
    alloc_str, 
    Ptr, 
    ListPtr, 
    IsCtx, 
    IsLiveCtx, 
    Store, 
    Env, 
    LiveZst, 
    HasNanodaDbg 
};


use Name::*;

pub type StringPtr<'a> = Ptr<'a, String>;
pub type NamePtr<'a> = Ptr<'a, Name<'a>>;
pub type NamesPtr<'a> = ListPtr<'a, Name<'a>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Name<'a> {
    Anon,
    Str(NamePtr<'a>, StringPtr<'a>),
    Num(NamePtr<'a>, u64),
}

impl<'a> Name<'a> {
    // This is the jankiest once since we have to deal with String.
    pub fn insert_env<'e>(self, env : &mut Env<'e>, live : &Store<LiveZst>) -> NamePtr<'e> {
        match self {
            Anon => unreachable!("Anon should always begin in the environment!"),
            Str(pfx, sfx) => {
                let pfx = pfx.insert_env(env, live);
                match sfx {
                    Ptr::E(index, _, z) => {
                        let sfx2 = env.store.strings.extend_safe(index, z);
                        assert_eq!(sfx, sfx2);
                        Str(pfx, sfx2).alloc(env)
                    },
                    Ptr::L(index, h, z) => {
                        let sfx = live.strings.get_elem(index, h, z).clone();
                        pfx.new_str(sfx, env)
                    }
                }
            },
            Num(pfx, sfx) => pfx.insert_env(env, live).new_num(sfx, env)
        }
    }
}


impl<'a> NamePtr<'a> {

    pub fn new_str(self, s : String, ctx : &mut impl IsCtx<'a>) -> NamePtr<'a> {
        Str(self, alloc_str(s, ctx)).alloc(ctx)
    }

    pub fn new_num(self, n : u64, ctx : &mut impl IsCtx<'a>) -> NamePtr<'a> {
        Num(self, n).alloc(ctx)
    }

    pub fn new_param(self, ctx : &mut impl IsCtx<'a>) -> LevelPtr<'a> {
        Param(self).alloc(ctx)
    }

    pub fn get_prefix(self, ctx : &impl IsLiveCtx<'a>) -> NamePtr<'a> {
        match self.read(ctx) {
            Anon => self,
            | Str(pfx, _)
            | Num(pfx, _) => pfx
        }
    }



}



impl<'a> HasNanodaDbg<'a> for Name<'a> {
    fn nanoda_dbg(self, ctx : &impl IsCtx<'a>) -> String {
        match self {
            Anon => String::new(),
            Str(pfx, sfx) if pfx.read(ctx) == Anon => {
                sfx.read(ctx).clone()
            }
            Str(pfx, sfx) => {
                format!("{}.{}", pfx.nanoda_dbg(ctx), sfx.read(ctx))
            }
            Num(pfx, sfx) if pfx.read(ctx) == Anon => {
                sfx.to_string()
            },
            Num(pfx, sfx) => {
                format!("{}.{}", pfx.nanoda_dbg(ctx), sfx.to_string())
            }
        }
    }
}



