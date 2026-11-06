# Smart Mutators Algorithm (v2)

The inductive datatype to mutate over has the form

```ml
Inductive <Dat> :=
  <for i>{ 
    | <DatCon i> : 
        (* parameters *)
        <for j>{_ : <DatConPrmTyp i,j>} ->
        (* recursive parameters *)
        <for k>{<DatConRecPrm i,k> : <Dat>} ->
        (* output *)
        <Dat>
  }
```

The inductive relation to mutate with respect to has the form

```ml
Inductive <Rel> : <for i>{<RelPrmType i> : Set} -> <Dat> -> Prop :=
  <for i>{ 
    | <RelCon i> : 
        (* parameters *)
        <for k>{<RelConPrm i,k> : <RelConPrmTyp i,k>} ->
        (* recursive paramters *)
        <for l>{<RecConRecPrm i,l> : <Dat>}
        (* hypotheses *)
        <for m>{<RelConHyp i,m> ->}
        (* inductive hypotheses *)
        <for n>{<Rel> <for i>{<RelConIndHypArg i,n,i>} <RelConIndHypArgDat i,n> ->}
        (* output *)
        <Rel> <for i>{<RelConArg i,i>} <RelConArgDat i>      
  }
```

Then, the mutation algorithm is the following:

```ml
Definition mut 
    `{Sized <Dat>}
    <for i,j>{`{Arbitrary <DatConPrmTyp j,j>}}
    `{ArbitrarySizeST (fun (x : <Dat>) => <Rel> <for i>{x<i> : <RelPrm i>} x}
    <for i>{<RelPrm i> : <RelPrmType i>}
    (x : <Dat>) : 
    option (G <Dat>) :=
  let n := size x in
  match x with
  <for i>{ (* range over <DatCon i> *)
  | <DatCon i> <for j>{<DatConPrm i,j>} <for k>{<DatConRecPrm i,k>} =>
    backtrack
      [ 
        (* regenerate: replace this node with a new generation *)
        (*    preserves size *)
        ( 1
        , bindGenOpt (arbitrarySizeST (fun x' => <Rel> <for i>{<RelPrm i>} x') (size x))
        )

        (* NOTE:
            Theres a common pattern is ranging over the relation constructors 
            that could possibly produce a relation on a term of a certain form,
            fixing the rest of the relation args. This involves unification, 
            which will further specify the form of the args to the data 
            constructor. Then the args ar concretized using generate/filter so 
            that. 
        *)

        (* NOTE:
            _recombine_ covers _regenerate arg_ as well, in the cases that the 
            recombination chooses the same constructor and fixes all args except
            for one to be regenerated.     
        *)

        (* NOTE:
              _recombine_ covers _mutate child_ then _regenerate_ as well, in 
              cases that recombination chooses the same constructor and fixes 
              all args except for one recursive args to be regenerated.  *)

        (* recombine: replace this node, using at least one of its args *)
        <for j>{ (* range over <DatCon j> *)
          <for k>{ (* range over <RelCon k> *)
            (* check that <RelCon k> can produce <Rel> <for i>{<RelPrm i>} <DatCon j> *)
            <if>{unify <RelConArgDat k> (<DatCon j> ... freshUniVar ...)} 
            <then>{
              ; ( 1 (* TODO: special weight? *)
                , (*  build/filter
                        <for l>{<RelConPrm k,l>}, <for m>{<RelConPrm k,l>}
                      such that they satisfy
                        <for n>{<RelConHyp k,n>}, o@{<RelConIndHyp k,o>}
                      using
                        <for j>{<DatConPrm i,j>} <for k>{<DatConRecPrm i,k>} *)
                  ret (Some (<RelConArgDat k>))
                )
            }
          }
        }

        (* regenerate arg: replace an arg with a fresh generation *)
        (*    non-recursive *)
        <for k>{ (* range over <RelCon k> *)
          <if>{unify (<RelConArgDat k>) x} {
            <for k>{ (* range over <DatConPrm i,j> *)
              ; ( 1 (* TODO: special weight? *)
              , (*  generate/filter 
                      <DatConPrm' i,j> 
                    such that it satisfies
                      <for n>{<RelConHyp k,n>}, o@{<RelConIndHyp k,o>} *)
                ret (Some (
                  <DatCon i>
                    j'@{<if>{j = j'} 
                          <then>{<DatConPrm' i,j'>} 
                          <else>{<DatConPrm i,j'>}} 
                    <for k>{<DatConRecPrm i,k>}))
              )
            }            
          }
        }
        
        (* mutate child: mutate a different node among this node's descendants *)
        <for k>{ (* range over <DatConRecPrm k> *)
          <for l>{ (* range over <RelCon l> *)
            (* TODO: conditions when can traverse mut via <RelCon l> *)
            <if>{...} <then>{
              ; ( size <DatConRecPrm k>
                  (* TODO: compute rest of args to mut from <RelCon l> *)
                , bindGenOpt (mut ... <DatConRecPrm k>) (fun <DatConRecPrm' k> =>
                  (* rebuild <DatCon i> giving <DatConRecPrm' k> in proper place *)
                  ret (Some (
                    <DatCon i> 
                      <for j>{<DatConPrm i,j>}
                      <for k'>{<if>{k = k'} 
                                <then>{<DatConRecPrm' k>}
                                <else>{<DatConRecPrm k>}}
                  ))) 
                )
            }
          }
        }
      ]
  }
  end
```