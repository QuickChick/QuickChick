# Smart Mutators Algorithm (v1)

The inductive datatype to mutate over has the form

```ml
Inductive <Dat> :=
  i@{ | <DatCon i> : 
          (* parameters *)
          j@{ _ : <DatConPrmTyp i,j> } ->
          (* recursive parameters *)
          k@{ <DatConRecPrm i,k> : <Dat> } ->
          (* output *)
          <Dat>
  }
```

The inductive relation to mutate with respect to has the form

```ml
Inductive <Rel> : i@{ <RelPrmType i> : Set } -> <Dat> -> Prop :=
  j@{ | <RelCon j> : 
          (* parameters *)
          k@{ <RelConPrm j,k> : <RelConPrmTyp j,k> } ->
          (* recursive paramters *)
          l@{ <RecConRecPrm j,l> : <Dat> }
          (* hypotheses *)
          m@{ <RelConHyp j,m> -> }
          (* inductive hypotheses *)
          n@{ <Rel> i@{ <RelConIndHypArg j,n,i> } <RelConIndHypArgDat j,n> -> }
          (* output *)
          <Rel> i@{ <RelConArg j,i> } <RelConArgDat j>      
  }
```

Then, the mutation algorithm is the following:

```ml
Definition mut 
    `{Sized <Dat>}
    i,j@{ `{Arbitrary <DatConPrmTyp j,j>} }
    `{ArbitrarySizeST (fun (x : <Dat>) => <Rel> i@{ x<i> : <RelPrm i> } x}
    i@{ <RelPrm i> : <RelPrmType i> }
    (x : <Dat>) : 
    option (G <Dat>) :=
  let n := size x in
  match x with
  j@{ (* range over dat cons: <DatCon j> *)
    <DatCon j> k@{ <DatConArg j,k> } l@{ <DatConRecArg j,l> } =>
      backtrack
        [ (* mut this *) 
          ( 1
          , arbitrarySizeST (fun x => <Rel> i@{ <RelPrm i> } x) n )
          k@{ (* range over rel cons: <RelCon k>  *)
            #if <RelConArgDat k> ~ x #then
              l@{ (* range over dat con args: <DatConArg j,l> *)
                (* mut arg <DatConArg j,l> *)
                ; ( 1   
                  , bindGenOpt 
                      ( (* 
                        generate/filter <DatConArg' j,l> such that 
                          <DatConArg' j,l> satisfies each m@{ <RelConHyp k,m> }
                          <DatConArg' j,l> satisfies each 
                            m,n@{ <RelConIndHyp k,m,n> }
                        which involves generating/filtering parameters 
                        not specified by the unification <RelConArgDat k> ~ x
                        *)
                      )
                      (fun <DatConArg' j,l> =>
                        ret (Some 
                          (<DatCon j> 
                              l'@{ if l == l'
                                    then <RelConArg' j,l'> 
                                    else <RelConArg  j,l'> })) )
                  )
              }
            #end
          }
          m@{ (* range over dat con rec args: <DatConRecArg j,m> *)
            (* mut rec arg <DatConRecArg j,m>  *)
            ; ( size <DatConRecArg j,m>
              , bindGenOpt
                  ( (* 
                    generate/filter <RelConRecArg' j,l> such that 
                      <RelConRecArg' j,l> satisfies each m@{ <RelConHyp l,m> }
                      <RelConRecArg' j,l> satisfies each n@{ <RelConIndHyp l,n> }
                      size <RelConRecArg' j,l> == size <RelConRecArg j,l>
                    which involves generating/filtering parameters 
                    not specified by the unification <RelConArgDat k> ~ x
                    *)
                  )
                  (fun <RelConArg' j,l> =>
                    ret (Some (<RelCon j> 
                      l'@{ if l == l'
                            then <RelConArg' j,l'> 
                            else <RelConArg  j,l'> })) )
              )
          }
        ]
  }
```
