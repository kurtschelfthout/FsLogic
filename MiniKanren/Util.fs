namespace MiniKanren

module Option =
    let defaultTo a opt =
        match opt with
        | None -> a
        | Some a -> a

[<AutoOpen>]
module Util =     
    let uncurry f = fun a b -> f (a,b)