module MiniKanren.Stream

//a good explantion of the need for all these cases is in the uKanren paper.
type Stream<'a> =
    | MZero
    | Unit of 'a
    | Choice of 'a * Stream<'a>
    | Inc of Lazy<Stream<'a>>

let result = Unit

let mzero = MZero

let rec mplus a b =
    match a with
    | MZero -> b
    | Unit a -> Choice (a,b)
    | Choice(a,b') -> Choice (a,mplus b b') //interesting - interleaving of the results here
    | Inc a' -> Inc (lazy mplus b a'.Value) 

let rec bind s g =
    match s with
    | MZero -> MZero
    | Unit a -> g a
    | Choice (a,b) -> mplus (g a) (bind b g)
    | Inc f -> Inc (lazy bind f.Value g)

let mplusMany streams = Seq.fold mplus mzero streams

let bindMany stream = Seq.fold bind stream

let delay f = Inc (lazy f())

type Stream<'a> with
    static member (>>=)(m,f) = bind m f
    static member (+++)(m1,m2) = mplus m1 m2

type StreamBuilder() =
    member __.Bind(m,f) = bind m f
    member __.Return a = result a
    member __.ReturnFrom a = a
    member __.Zero = mzero
    member __.Combine(m1,m2) = mplus m1 m2
    member __.Delay f = delay f

let stream = StreamBuilder()