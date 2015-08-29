namespace MiniKanren

module internal Option =
    let defaultTo a opt =
        match opt with
        | None -> a
        | Some a -> a

    let getOrFail s opt =
        match opt with
        | None -> failwith s
        | Some v -> v

[<AutoOpen>]
module internal Util =  
    let flip f = fun b a -> f a b   
    let curry f = fun a b -> f (a,b)
    let uncurry f = fun (a,b) -> f a b
    /// Convenience active pattern to find a key in a map.
    let (|Find|_|) map key = Map.tryFind key map
