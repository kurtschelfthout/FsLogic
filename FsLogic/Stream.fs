namespace FsLogic

//a good explantion of the need for all these cases is in the uKanren paper.
type Stream<'a> =
    | MZero
    | Unit of 'a
    | Choice of 'a * Stream<'a>
    | Inc of Lazy<Stream<'a>>

module Stream =

    let unit = Unit

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

    let rec map f = function
        | MZero -> MZero
        | Unit a -> Unit (f a)
        | Choice (a,b') -> Choice (f a,map f b')
        | Inc a' -> Inc (lazy map f a'.Value)

    let mplusMany streams = Seq.fold mplus mzero streams

    let bindMany stream = Seq.fold bind stream

    let delay f = Inc (lazy f())

    type StreamBuilder internal() =
        member __.Bind(m,f) = bind m f
        member __.Return a = unit a
        member __.ReturnFrom a = a
        member __.Zero = mzero
        member __.Combine(m1,m2) = mplus m1 m2
        member __.Delay f = delay f

    let stream = StreamBuilder()

    let rec toSeq f =
        seq { match f with
              | MZero -> ()
              | Inc (Lazy s) -> yield! toSeq s
              | Unit a -> yield a
              | Choice(a,f) ->  yield a; yield! toSeq f
            }


type Stream<'a> with
    static member (>>=)(m,f) = Stream.bind m f
    static member (+++)(m1,m2) = Stream.mplus m1 m2

[<AutoOpen>]
module General =
    let inline (>=>) f g = fun x -> f x >>= g