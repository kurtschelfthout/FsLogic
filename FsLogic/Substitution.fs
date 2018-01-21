namespace FsLogic

module Substitution = 

    open System.Threading

    ///Set this to true to check after 
    ///unifying whether adding any new substitutions
    ///would introduce a circularity. This is
    ///an expensive check so is turned off by
    ///default.
    let mutable occursCheck = true

    ///The id of variables.
    type internal VarId = int

    let private nextVarId = 
        let varcount = ref 0
        fun () -> Interlocked.Increment(varcount) : VarId

    type internal TagId = int

    type ReifiedTerm =
        | Free of int
        | Det of obj
        | Half of list<ReifiedTerm> with
        static member IsDetermined rterm =
            match rterm with Det _ -> true | _ -> false
        static member GetDeterminedValue rterm =
            match rterm with Det v -> v | _ -> failwithf "Reified term %A is not fully determined." rterm
        static member ToOption rterm =
            match rterm with Det v -> Some v | _ -> None

    /// The universal type that holds untyped, tagged representations
    /// of all our terms. A term can be either:
    /// - a variable Var
    /// - a constructor Ctor: this represents structured terms that can be unified structurally
    ///   with other terms with the same tag.
    /// - an atom Atom: this is an unstructured term that can be unified if their values are equal as
    ///   determined by F#'s (=) operator.
    [<CustomEquality; NoComparison>]
    type Term = 
        | Var of VarId
        | Ctor of (list<Term> -> ReifiedTerm) * tag:TagId * list<Term>
        | Atom of obj with
        ///Equals defined just to make testing easier.
        override t.Equals(other) =
            match other with
            | :? Term as other ->
                match (t,other) with
                | (Var i, Var j) -> i = j
                | (Ctor (_, p1, i1), Ctor (_, p2,i2)) -> p1 = p2 && i1 = i2
                | (Atom o1, Atom o2) -> o1 = o2
                | _ -> false
            | _ -> false

    /// Create an untyped new variable.
    let newVar() = Var <| nextVarId()

    /// A substitution associates a variable with a term which may again be a variable.
    /// This way of representing substitutions is called a triangular substitution.
    type Subst = Map<VarId,Term>

    /// Extend a substitution with a new var -> term mapping without checking for
    /// circularities. A circularity can occur for example by associating var a -> var b,
    /// then associating var b -> var a. This will cause walk, below, to diverge.
    let extNoCheck : _ -> _ -> Subst -> Subst = Map.add

    /// Repeatedly lookup the term v in the subsitution until it's no longer a variable,
    /// or it can't be found, and return the result.
    /// In other words, if we imagine the substitution as representing a 
    /// set of trees, where each mapping var -> term brings us closer to the root of a tree,
    /// then this method finds the root of the tree v is a part of.
    let rec walk term (s:Subst) =
        match term with
        | Var (Find s rhs) -> walk rhs s
        | _ -> term

    /// Returns true if adding an association between x and v
    /// would introduce a circularity.
    /// A circularity would in the first instance cause walk to diverge
    /// (loop infinitely).
    /// This is commonly called the occurs check.
    let rec occurs (varId:VarId) term s =
        let vs = walk term s
        match vs with
        | Var id' -> id'.Equals(varId)
        | Ctor (_,_,fields) -> Seq.exists (fun exp -> occurs varId exp s) fields
        | Atom _ -> false

    /// Calls extNoCheck only if the occurs call returns false.
    /// If the global variable 'occursCheck' is false, just skips
    /// the occursCheck and so is equivalent to extNoCheck.
    let ext varId term s =
        if occursCheck && occurs varId term s then 
            None
        else 
            Some <| extNoCheck varId term s

    /// This represents the constraint that all (variable, term) pairs can not be simultaneously unifiable.
    /// In other words, the constraint holds iff the list contains at least one pair that is not
    /// unifiable.
    type DisequalityConstraint = list<VarId * Term> //maybe Subst?

    /// A list of constraints.
    type ConstraintStore = list<DisequalityConstraint> 

    /// We package substitutions and constraints in one datatype to easily pass it around.
    type Package = { Substitution: Subst
                     ConstraintStore: ConstraintStore } with
        static member Empty = { Substitution=Map.empty; ConstraintStore = []}

    /// Unifies two terms u and v with respect to the substitution s. Returns
    /// Some s': a potentially extended substitution s' if unification succeeds.
    /// None: if unification fails or would introduce a circularity (the latter is only checked
    ///       if the occurs check is enabled.)
    let rec unify u v s = 
        let unifySubExprs exprs1 exprs2 =
            let merge subst (e1,e2) = 
                subst 
                |> Option.bind (unify e1 e2)
            Seq.zip exprs1 exprs2
            |> Seq.fold merge (Some s)
        let u' = walk u s //remember: if u/v is a variable it will return what it's associated with;
        let v' = walk v s //otherwise, it will just return u or v itself.
        match (u',v') with
        | Var uId, Var vId when uId = vId -> Some s
        | Var uId, Var _ -> Some (extNoCheck uId v' s) //distinct, unassociated vars never introduce a circularity, hence extNoCheck.
        | Var uId, _ -> ext uId v' s
        | _, Var vId -> ext vId u' s
        | Atom u, Atom v when u = v -> Some s
        | Ctor (_,i,ufields), Ctor (_,j,vfields) when i = j ->  unifySubExprs ufields vfields
        | _ -> None

    let rec internal unifySubExprs exprs1 exprs2 s =
            let merge subst (e1,e2) = 
                subst 
                |> Option.bind (fun (subst,ext) -> unifyExt e1 e2 subst |> Option.map (fun (s,e) -> (s, e @ ext)))
            Seq.zip exprs1 exprs2
            |> Seq.fold merge (Some (s,[]))

    /// Unifies two terms u and v with respect to the substitution s, and keeps track of what it extends
    /// the substitution with, for use in disunify. Returning
    /// Some (s',l): a potentially extended substitution s' if unification succeeds, l containing 
    ///              a list of pairs with which it was extended. The latter is for consumption by disunify.
    /// None: if unification fails or would introduce a circularity (the latter is only checked
    ///       if the occurs check is enabled.)
    and unifyExt u v s = 
        let u = walk u s //remember: if u/v is a variable it will return what it's associated with;
        let v = walk v s //otherwise, it will just return u or v itself.
        match (u,v) with
        | Var u, Var v when u = v -> Some (s,[])
        | Var u, Var _ -> Some ((extNoCheck u v s), [u,v]) //distinct, unassociated vars never introduce a circularity, hence extNoCheck.
        | Var u, _ -> ext u v s |> Option.map (fun s -> s,[u,v])
        | _, Var v -> ext v u s |> Option.map (fun s -> s,[v,u])
        | Atom u, Atom v when u = v -> Some (s,[])
        | Ctor (_,i,ufields), Ctor (_,j,vfields) when i = j ->  unifySubExprs ufields vfields s
        | _ -> None

    /// Substitutes the term and its subterms with what they are associated with in the substitution,
    /// in other words looks inside Ctor, recursively.
    let rec walkMany term s =
        let v = walk term s
        match v with
        | Ctor (f,i,exprs) -> exprs |> List.map (fun e -> walkMany e s) |> (fun es -> Ctor(f,i,es))
        | _ -> v

    /// Reify the term given the substitution. This means, remove variables as much as possible,
    /// and clean up those that remain by re-numbering them in increasing order. 
    let reify term s =
        //Renumber all remaining variables in an expression with names in increasing order.
        let rec reifyS v s =
            let v = walk v s
            match v with
            | Var i -> 
                //we use negative VarIds here, because positive ones may already be taken.
                extNoCheck i (Var -s.Count) s 
            | Ctor (_,_,fields) -> 
                fields |> List.fold (fun s field -> reifyS field s) s
            | _ -> s
        let v = walkMany term s
        walkMany v (reifyS v Map.empty)