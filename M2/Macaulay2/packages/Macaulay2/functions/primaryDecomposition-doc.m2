--- status: TODO
--- author(s): 
--- notes: 

undocumented (primaryDecomposition,MonomialIdeal)
document { 
     Key => {primaryDecomposition,(primaryDecomposition,Ideal)},
     Headline => "irredundant primary decomposition of an ideal",
     Usage => "primaryDecomposition I",
     Inputs => {
	  "I" => { OFCLASS Ideal, " or ", OFCLASS MonomialIdeal, " in a (quotient of a) polynomial ring ", TT "R", "."}
	  },
     Outputs => {
	  List => {"of ", TO2(Ideal,"ideals"), ", a minimal list of primary ideals whose intersection is ", TT "I"}
	  },
     "This routine returns an irredundant primary decomposition
     for the ideal ", TT "I", ".  The specific algorithm used varies
     depending on the characteristics of the ideal, and can also be specified
     using the optional argument ", TT "Strategy", ".",
     PARA,
     "Primary decompositions algorithms are very sensitive to their input.  Some
     algorithms work very well on certain classes of ideals, but poorly on other classes.
     If this function seems to be taking too long, try another algorithm (using ",
     TO [primaryDecomposition,Strategy], ").",
     EXAMPLE {
	  "R = QQ[a..i];",
	  "I = permanents(2,genericMatrix(R,a,3,3))",
          "C = primaryDecomposition I;",
	  "I == intersect C",
	  "#C",
	  },
     PARA,
     "Recall that ", TO (symbol/,List,Function), " applies a function to each element of a
     list, returning the results as a list.  This is often useful with lists of ideals,
     such as the list ", TT "C", " of primary components.",
     EXAMPLE {
	  "C/toString/print;",
	  "C/codim",
	  "C/degree"
	  },
     PARA,
     "The corresponding list of associated prime ideals is cached in ", TT "I.cache.ass", ",
     and can be obtained by using ", TO (ass,Ideal), ".",
     EXAMPLE {
	  "ass I / print;"
	  },
     Caveat => {"The ground ring must be a prime field."},
     SeeAlso => {PrimaryDecomposition,(ass,Ideal), radical, decompose, topComponents, removeLowestDimension}
     }

document { 
     Key => [primaryDecomposition, PrintLevel],
     PARA {
	  "The value of this option is passed on to the ", TO "associatedPrimes", " routine, which is called during the computation."
	  },
     SeeAlso => { [associatedPrimes, PrintLevel] }
     }
