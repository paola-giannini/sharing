I think we could have a a module like

Module Type SharingRelation.
   
and a sharing relation on a list of atoms (variables)

       shRel (l:list atom) could be

an equivalence relation on a vector of atoms of length  (length l) +1
 
        eqRel (t atom ((length l)+1) ).

where t atom ((length l) +1) is the type of a vector with elements of type atom
and indices from 0 to (length l)+1

I think that could be convenient to have the elements of l to be in the
vector either
    a) from 0 to ((length l) - 1) and consider the element in position 
    (length l) to correspond the the metavariable associated with the result
    of an expression, or 
    b) from 1 to (length l) and consider the element in position 
    0 to correspond the the metavariable associated with the result.

In the following I indicate this metavariable with res,
however, I think that we do not need to have an explicit name for it.

Should not be difficult to define the function that given a list of atoms
returns the corresponding vector 
 
     vect_from_list (l:list atom) -> t atom ((length l) +1)


What we need for the type checking judgment is: 

1) given a list of atoms l the sharing relation which is the identity
on the elements of the list of atoms l + res

     id_shRel l :  shRel l  

2) a function that given a sharing relation on l, shR, and an element of 
l, x, returns the smallest sharing relation the same domain in
which x is equivalent to res. Searching for the position of x  should be 
consistent with how, see 5), we define removing/adding elements to a
sharing relation

     add_eq_res (shR: shRel l) (x: atom) -> (shR: shRel l)

3) a function that given a sharing relation on l, shR, makes res into
an element which is not in equivalence with any other element:

     rem_res (shR: shRel l) -> (shR: shRel l)

4) given  two sharing relations on (the same) list of atoms l, shR1 and 
shR2, a function (or operator +) that returns the smallest sharing  
relation on l containing shR1 and shR2. We may assume that in both
shRes1 and shRes2 the variable res is not equivalent to any other
variable (to enforce this we should first apply rem_res to shRes1 and shRes2)
  
    "+" (shR1: shRel l) (shR2: shRel l) -> (shR: shRel l)
    
CHANGE: We need a sum that simply does the sum, including putting together
the equivalance classes of res (used in rules [T-FIELD-ACCESS] and [T-NEW])    
    

5) given a sharing relation on a list of atoms l such that
      l=l1+l2 
a function that returns the restriction of the relation to l1. 

   restrict_res (shR: shRel l) (l1:list var)-> (shR: shRel l1)

CHANGE: for res we just keep its equivalence relation after removing the 
varibales in l1 
NOTE: l1 must be an intial segment of l!



   
6) a function that given a sharing relation on l, shR, an element of 
l, x, and a subset of the atoms of l, X, returns the smallest sharing 
relation on l in which x is equivalent to all the variables in X. 


     add_eq_X (shR: shRel l) (x: atom) (X: list atom) -> (shR: shRel l)

IMPORTANT: should work also when X is the empty set.  
If, for the moment, we consider the language without method call, we DO NOT
NEED 6)

It is not yet clear to me, what kind of assertions we need to have on this
functions. I guess we will discover it when trying to do the proof of soundness.



7) given a sharing relation  a predicate
        capsule shR
which is true (or hold?) if the equivalence class of res is a singleton.        

8) given a sharing relation  a function
        eq_res shR  -> list var
which returns the list of variables equivalent to res in shR


IMPORTANT:

In general in the (list atom) on which the sharing relation is defined
there could be duplicate elements (atoms). However, environments are
built in such a way that the "current atom" is the first. So in 4)
we are removing the last atom added.








