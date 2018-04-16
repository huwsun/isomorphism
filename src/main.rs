#![allow(dead_code)]

/// so, when are two type, `a` and `b`, considered equal?
/// a definition might be, it is possible to go from `a` to `b`,
/// and from `b` to `a`.
/// Going a roundway trip should leave you the same value.
/// Unfortunately it is virtually impossible to test this.
/// This is called ISO.
pub enum Void {}

impl PartialEq for Void {
    fn eq(&self, _: &Void) -> bool {
        true
    }
}

pub fn absurd(_: Void) -> ! {
    panic!("You must be kidding! Where did you find that void instance?");
}

pub type ISO<A, B> = (Box<Fn(A) -> B>, Box<Fn(B) -> A>);

pub fn iso<A: 'static, B: 'static, F1, F2>(a: F1, b: F2) -> ISO<A, B>
    where F1: 'static + Fn(A) -> B,
          F2: 'static + Fn(B) -> A,
{
    (Box::new(a), Box::new(b))
}

/// given ISO a b, we can go from a to b
pub fn sub_st_l<A, B>(iso: ISO<A, B>) -> Box<Fn(A) -> B> { iso.0 }

/// and vise versa
pub fn sub_st_r<A, B>(iso: ISO<A, B>) -> Box<Fn(B) -> A> { iso.1 }

/// There can be more than one ISO a b
pub fn iso_bool() -> ISO<bool, bool> {
    iso(|a| { a }, |a| { a })
}

pub fn iso_bool_not() -> ISO<bool, bool> {
    iso(|a: bool| { !a }, |a: bool| { !a })
}

/// isomorphism is reflexive
pub fn refl<A: 'static>() -> ISO<A, A> {
    iso(|a| { a }, |a| { a })
}

/// isomorphism is symmetric
pub fn symm<A: 'static, B: 'static>(i: ISO<A, B>) -> ISO<B, A> {
    (i.1, i.0)
}

/// isomorphism is transitive
pub fn trans<A: 'static, B: 'static, C: 'static>
(ab: ISO<A, B>, bc: ISO<B, C>) -> ISO<A, C> {
    let (ab, ba) = ab;
    let (bc, cb) = bc;
    iso(move |a| bc(ab(a)), move |c| ba(cb(c)))
}

/// we can combine isomorphism
pub fn iso_tuple<A: 'static, B: 'static, C: 'static, D: 'static>
(ab: ISO<A, B>, cd: ISO<C, D>) -> ISO<(A, C), (B, D)> {
    let (ab, ba) = ab;
    let (cd, dc) = cd;
    iso(move |(a, c)| (ab(a), cd(c)), move |(b, d)| (ba(b), dc(d)))
}

pub fn iso_vec<A: 'static, B: 'static>(i: ISO<A, B>) -> ISO<Vec<A>, Vec<B>> {
    let (l, r) = i;
    iso(move |av: Vec<A>| av.into_iter().map(|a| l(a)).collect(), move |bv: Vec<B>| bv.into_iter().map(|b| r(b)).collect())
}

pub fn iso_option<A: 'static, B: 'static>
(i: ISO<A, B>) -> ISO<Option<A>, Option<B>> {
    let (l, r) = i;
    iso(move |opta: Option<A>| match opta {
        Some(a) => Some(l(a)),
        None => None
    }, move |optb: Option<B>|
            match optb {
                Some(b) => Some(r(b)),
                None => None
            })
}

pub fn iso_result<A: 'static, B: 'static, C: 'static, D: 'static>
(ab: ISO<A, B>, cd: ISO<C, D>) -> ISO<Result<A, C>, Result<B, D>> {
    let (ab, ba) = ab;
    let (cd, dc) = cd;
    iso(
        move |r: Result<A, C>| match r {
            Ok(a) => Ok(ab(a)),
            Err(c) => Err(cd(c))
        },
        move |r: Result<B, D>| match r {
            Ok(b) => Ok(ba(b)),
            Err(d) => Err(dc(d))
        },
    )
}

/// Going another way is hard (and is generally impossible)
/// Remember, for all valid ISO, converting and converting back
/// is the same as the original value.
/// You need this to prove some case are impossible.
pub fn iso_un_option<A: 'static, B: 'static>
(i: ISO<Option<A>, Option<B>>) -> ISO<A, B> {
    let (l, r) = i;
    iso(
        move |a: A| match l(Some(a)) {
            Some(b) => b,
            None => l(None).unwrap()
        },
        move |b: B| match r(Some(b)) {
            Some(a) => a,
            None => r(None).unwrap()
        },
    )
}

/// inf + 0 = inf + 1
pub fn iso_eu() -> ISO<Result<Vec<()>, ()>, Result<Vec<()>, Void>> {
    iso(
        move |r: Result<Vec<()>, ()>| match r {
            Ok(mut v) => {
                v.push(());
                Ok(v)
            }
            Err(_e) => (Ok(vec![]))
        },
        move |r: Result<Vec<()>, Void>| match r {
            Ok(mut v) => {
                if v.len() == 0 { Err(()) } else {
                    v.pop();
                    Ok(v)
                }
            }
            Err(_e) => unreachable!(),
        },
    )
}

pub type IsoFL<A, B, C, D> = Box<FnOnce(Box<Fn(A) -> C>) -> Box<FnOnce(B) -> D>>;
pub type IsoFR<A, B, C, D> = Box<FnOnce(Box<Fn(B) -> D>) -> Box<FnOnce(A) -> C>>;
pub type IsoF<A, B, C, D> = (IsoFL<A, B, C, D>, IsoFR<A, B, C, D>);

/// translator note:
/// FnBox is not yet supported, we can only return an uncallable
/// Box<FnOnce> (RetFunc). You should return the function with
/// correct type, which will be checked by the tests.
/// The type annotation is shown above. You need you return something like
/// (Box::new(...), Box::new(...))
pub fn iso_func<A: 'static, B: 'static, C: 'static, D: 'static>
(ab: ISO<A, B>, cd: ISO<C, D>) -> IsoF<A, B, C, D> {
    let (ab, ba) = ab;
    let (cd, dc) = cd;
    (
        Box::new(|f: Box<Fn(A) -> C>| Box::new(move |b: B| cd(f(ba(b))))),
        Box::new(|f: Box<Fn(B) -> D>| Box::new(move |a: A| dc(f(ab(a)))))
    )
}

/// And we have isomorphism on isomorphism!
pub fn iso_symm<A: 'static, B: 'static>() -> ISO<ISO<A, B>, ISO<B, A>> {
    iso(symm, symm)
}


#[test]
fn sub_st_l_test() {
    assert!(sub_st_l(iso_bool())(true));
    assert!(!sub_st_l(iso_bool())(false));
    assert!(sub_st_l(iso_bool_not())(false));
}
