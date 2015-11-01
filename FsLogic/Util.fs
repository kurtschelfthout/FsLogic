namespace FsLogic

[<AutoOpen>]
module internal Util =
    let flip f = fun b a -> f a b
    let curry f = fun a b -> f (a,b)
    let uncurry f = fun (a,b) -> f a b
    /// Convenience active pattern to find a key in a map.
    let (|Find|_|) map key = Map.tryFind key map
