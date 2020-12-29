-- -*- coding: utf-8 -*-
-- -*- coding: utf-8 -*-
document {
     Key => "ideals",
     HEADER2 "An overview",     
     "In Macaulay2, once a ring (see ",TO "rings", 
     ") is defined, ideals are constructed in the usual way
     by giving a set of generators.",
     Subnodes => {
	  TO "creating an ideal",
	  "conversions",
	  TO "ideals to and from matrices",
	  TO "ideals to and from modules",
	  "basic operations on ideals",
	  TO "sums, products, and powers of ideals",
	  TO "equality and containment",
	  TO "extracting generators of an ideal",
	  TO "dimension, codimension, and degree",
	  "components of ideals",
	  TO "intersection of ideals",
	  TO "Saturation :: ideal quotients and saturation",
	  TO "MinimalPrimes :: radical of an ideal",
	  TO "MinimalPrimes :: minimal primes of an ideal",
	  TO "PrimaryDecomposition :: associated primes",
	  TO "PrimaryDecomposition :: primary decomposition",
	  -- TO "Gröbner bases", -- already referred to in the Mathematical Overview
	  },
     PARA{},
     "For those operations where we consider an ideal as a module, such
     as computing Hilbert functions and polynomials, syzygies, 
     free resolutions, see ",
     TO "modules", ".",
     PARA{},
      "For additional common operations and a comprehensive list of all routines
     in Macaulay2 which return or use ideals, see ", TO "Ideal", ".",
     PARA{},						    -- debug me!!
     "The following link differs from the previous one in case only: ", 
     TO "ideal", "."
     }

document {
     Key => "creating an ideal",
    
    SUBSECTION "ideal",
      "An ideal ", TT "I", " is represented by its generators.  
      We use the function ", TO "ideal", " to construct an ideal.",
      EXAMPLE {
	   "R = QQ[a..d];",
	   "I = ideal (a^2*b-c^2, a*b^2-d^3, c^5-d)"
	   },

    SUBSECTION "monomial ideals",
      "For a monomial ideal you can use the 
      function ", TO "monomialIdeal", ".",
      EXAMPLE {
	   "J = monomialIdeal (a^2*b, b*c*d, c^5)"
	   },
      "The distinction is small since a monomial ideal can be 
      constructed using ", TT "ideal", " .  However, there are a 
      few functions, like ", TO "PrimaryDecomposition::primaryDecomposition", " that run
      faster if you define a monomial ideal 
      using ", TT "monomialIdeal", ".",

    SUBSECTION "monomialCurveIdeal",
      "An interesting class of ideals can be obtained as the 
      defining ideals in projective space of monomial curves.  
      For example the twisted cubic is the closure of the set of 
      points ", TT "(1,t^1,t^2,t^3)", " in projective space.  We 
      use a list of the exponents and ", TO "monomialCurveIdeal", " to 
      get the ideal.",
      EXAMPLE {
	   "monomialCurveIdeal(R,{1,2,3})"
	   },
      SeeAlso => {
	   ideal,
	   monomialIdeal,
	   monomialCurveIdeal
	   }
    }

document {
     Key => "ideals to and from matrices",
     
     SUBSECTION "forming an ideal from a matrix",
       "After defining a matrix (see ", TO "inputting a matrix", ")
       , ", TT "M", ", the ideal generated by the entries of the matrix 
       is obtained using the command ", TO "ideal", ".",
       EXAMPLE {
	    "R = ZZ/101[a..e];",
	    "M = matrix{{a^2*b-c^2, a*b^2-d^3, c^5-d},{a^2*b, b*c*d, c^5}}",
	    "ideal M"
	    },

     SUBSECTION "forming a matrix from an ideal",
       "In much the same way we can construct a 1 by 
       n (where n is the number of generators of ", TT "I", "), 
       matrix from the n generators of an ideal ", TT "I", " using 
       the command, ", TO "generators", ".",
       EXAMPLE {
	    "I = ideal(a^2*b-c^2+c*d, a*b^2-b*d^3, c^5,d+e);",
	    "generators I"
	    },
       "The abbreviation ", TT "gens", " can be used for ", TT "generators", "." 
     }

document {
     Key => "ideals to and from modules",
     
     SUBSECTION "from ideals to modules",
       --     "There are two main ways to consider an ideal as 
       --     a module.  First, as a submodule of the rank one free 
       --     module, ", TT "R", " as the image of the map defined 
       --     by the 1 by n matrix consisting of the generators. The 
       --     easiest way to do this is to use the 
       --     function ", TT "module", ".",
       "An ideal ", TT "I", " is also an ", TT "R", "-submodule.  In
       Macaulay2 we distinguish between when we are thinking of ", TT "I", " as
       as ideal or a module.  If it is first defined as an ideal, it is easily
       turned into a module using the function ", TO "module", " and for any
       submodule of the rank one free module ", TT "R", " we can obtain an ideal 
       of the generators using the function ", TO "ideal", ".",
       EXAMPLE {
	    "R = ZZ/32003[x,y,z];",
	    "I = ideal(x^2,y*z-x);",
	    "module I"
	    },

     SUBSECTION "from modules to ideals",
       "For any submodule of the rank one free 
       module ", TT "R", " we can obtain an ideal of the generators 
       using the function ", TO "ideal", ".",
       EXAMPLE {
	    "A = matrix{{x*y-z,z^3}};",
	    "M = image A",
	    "ideal M",
	    },

     SUBSECTION "getting the quotient module corresponding to an ideal",
 "We also often work with ", TT "R/I", " as 
       an ", TT "R", "-module.  Simply typing ", TT "R/I", " at a prompt
       in Macaulay2 constructs the quotient ring (see ", 
       TO "quotient rings", ").  
       There are two ways to tell Macaulay2 that we want to work with this 
       as a module.",
       EXAMPLE {
	    "coker generators I",
	    "R^1/I"
	    },

     SUBSECTION "modules versus ideals for computations",
       "Some functions in Macaulay2 try to make an informed decision 
       about ideal and modules.  For example, if ", TO "resolution", " is
       given an ideal ", TT "I", ", it will compute a resolution of
       the module ", TT "R^1/I", ", as in the following example.",
       EXAMPLE {
	    --"J = ideal(x*y-z^2,x*z^3-y^4);",
	    "resolution I"
	    },
       "The functions ", TO "dim", " and ", TO "degree", " also 
       operate on ", TT "R^1/I", " if the input 
       is ", TT "I", " or ", TT "R^1/I", ".  However, the 
       function ", TO "hilbertPolynomial", " computes the Hilbert 
       polynomial of the module ", TT "I", " if the input 
       is ", TT "hilbertPolynomial I", ".",     
       PARA{}, "For basic information about working with 
       modules see ", TO "modules", "."
     }

document {
     Key => "sums, products, and powers of ideals",
     "Arithmetic for ideals uses the standard symbols.  Below are examples 
     of the basic arithmetic functions for ideal.", 
     EXAMPLE {
	  "R = ZZ/101[a..d]/(b*c-a*d,c^2-b*d,b^2-a*c);",
	  },
     "For more information about quotient rings see ", TO "quotient rings", ".",
     EXAMPLE {
	  "I = ideal (a*b-c,d^3);",
	  "J = ideal (a^3,b*c-d);",
	  "I+J",
	  "I*J",
	  "I^2"
	  },
     "For more information see ", TO (symbol+,Ideal,Ideal), ", 
     ", TO (symbol*,Ideal,Ideal), ", and ", TO (symbol^,Ideal,ZZ), "."
     }

document {
     Key => "equality and containment",
     "Equality and containment between two ideals in a polynomial ring 
     (or quotient of a polynomial ring) is checked by comparing their 
     respective Groebner bases.",     
     SUBSECTION "equal and not equal",
       "Use ", TO (symbol==,Ideal,Ideal), " to test if two ideals in 
       the same ring 
       are equal.",
       EXAMPLE {
	    "R = QQ[a..d];",
	    "I = ideal (a^2*b-c^2, a*b^2-d^3, c^5-d);",
	    "J = ideal (a^2,b^2,c^2,d^2);",
	    "I == J",
	    "I != J",
	    },

     SUBSECTION "normal form with respect to a Groebner basis and membership",
       "The function ", TO (symbol%,RingElement,Ideal), 
       " reduces an element with 
       respect to a Groebner basis of the ideal.", 
       EXAMPLE {
	    "(1+a+a^3+a^4) % J"
	    },
       "We can then test membership in the ideal by comparing 
       the answer to 0 using ", TO "==", ".",
       EXAMPLE {
	    "(1+a+a^3+a^4) % J == 0",
	    "a^4 % J == 0",
	    },

     SUBSECTION "containment for two ideals",
       "Containment for two ideals is tested 
       using ", TO "isSubset", ".",
       EXAMPLE {
	    "isSubset(I,J)",
	    "isSubset(I,I+J)",
	    "isSubset(I+J,I)"
	    },

     SUBSECTION "ideal equal to 1 or 0",
       "Use the expression ", TT "I == 1", " to see if the 
       ideal is equal to the ring.  Use ", TT "I == 0", " 
       to see if the ideal is identically zero in the given ring.",
       EXAMPLE {
	    "I = ideal (a^2-1,a^3+3);",
	    "I == 1",
	    "S = R/I",
	    "S == 0"
	    },
     SeeAlso => {
	  (symbol==,Ideal,Ideal),
	  (symbol==,Ideal,ZZ),
	  symbol!=,
	  (symbol%,RingElement,Ideal),
	  (isSubset,Ideal,Ideal),
	  "MinimalPrimes :: radicalContainment"
	  }
     }     

document {
     Key => "extracting generators of an ideal",
     
     SUBSECTION "obtain a single generator as an element",
       "Once an ideal has been constructed it is possible to 
       obtain individual elements using ", TO "_", ".   As 
       always in Macaulay2, indexing starts at 0. ",
       EXAMPLE {
	    "R = ZZ[w,x,y,z];",
	    "I = ideal(z*w-2*x*y, 3*w^3-z^3,w*x^2-4*y*z^2,x);",
	    "I_0",
	    "I_3"
	    },

     SUBSECTION "the generators as a matrix or list of elements",
       "Use ", TO "generators", " or its abbreviation ", TO "gens", " to 
       get the generators of an ideal ", TT "I", " as a matrix.  
       Applying ", TT "first entries", " to this matrix converts it 
       to a list.",
       EXAMPLE{
	    "gens I",
	    "first entries gens I"
	    },

     SUBSECTION "number of generators",
       "The command ", TO "numgens", " gives the number of generators 
       of an ideal ", TT "I", ".",
       EXAMPLE{
	    "numgens I"
	    },

     SUBSECTION "minimal generating set",
       "To obtain a minimal generating set of a homogeneous ideal 
       use ", TO "mingens", " to get the minimal generators as a matrix 
       and use ", TO "trim", " to get the minimal generators as an ideal.",
       EXAMPLE {
	    "mingens I",
	    "trim I"
	    },
 "The function ", TT "mingens", " is only well-defined for a 
       homogeneous ideal or in a local ring.  However, one can still try to 
       get as small a generating set as possible and when it is implemented
       this function will be done by ", TT "trim", ".",

     SUBSECTION "obtaining the input form of an ideal",
       "If the ideal was defined using a function 
       like ", TT "monomialCurveIdeal", " and the generators 
       are desired in the usual format for input of an ideal, the 
       function ", TO "toString", " is very useful. 
       (Note:  We are changing rings because ", TO "monomialCurveIdeal", " 
	    is not implemented for rings over ", TO "ZZ", ".)",
       EXAMPLE {
	    "R = QQ[a..d];",
	    "I = monomialCurveIdeal(R,{1,2,3});",
	    "toString I"
	    }
     }

document {
     Key => "dimension, codimension, and degree",
     "Use ", TO "dim", ", ", TO "codim", ", and ", TO "degree", " to 
     compute the dimension, codimension and degree, respectively, 
     of an ideal.  The functions ", TO "dim", " and ", TO "degree", " compute 
     the dimension and degree of the ring ", TT "R/I", ".",
     EXAMPLE {
	  "R = ZZ/101[x,y,z];",
	  "I = ideal(x^3-y*z^2,x*y-z^2,x*z);",
	  "dim I",
	  "codim I",
	  "degree I",
	  }
     }

document {
     Key => "intersection of ideals",
     "Use ", TO "intersect", " to compute the intersection of two or 
     more ideals.",
     EXAMPLE {
	  "R = QQ[a..d];",
	  "intersect(ideal(a,b),ideal(c*d,a*b),ideal(b*d,a*c))"
	  },
     "The command ", TO "intersect", " will only work with proper
     ideals. To intersect an ideal with a ring, use ",
     TO "selectInSubring", " along with the elimination ordering, see ", TO "Eliminate", "."
     }

end

This node is old -- is there anything we want to save from it?

document {
     Key => "ideals",
     "An ideal ", TT "I", " is represented by its generators,
     which are stored inside it in a one-rowed matrix.",
     PARA{},
     "The ideal generated by a list of ring elements can be constructed with the function
     ", TO "ideal", ".",
     EXAMPLE {
	  "R = ZZ/101[a..d];",
      	  "I = ideal (a^2*b-c^2, a*b^2-d^3, c^5-d)",
	  },
     "If you have a matrix, then ", TT "ideal", " will produce the ideal generated
     by the entries of the matrix.",
     EXAMPLE {
	  "f = matrix {{a^2,b^2},{c^2,d^2}}",
      	  "J = ideal f",
	  },
     "An interesting class of ideals can be obtained as the defining ideals in 
     projective space of monomial curves.  The twisted cubic is the closure of the
     set of points ", TT "(1,t^1,t^2,t^3)", " in projective space.  We use a list of
     the exponents and ", TO "monomialCurveIdeal", " to get the ideal.",
     EXAMPLE "monomialCurveIdeal(R,{1,2,3})",
     "The command ", TO "substitute", " can be used to transfer an ideal to another
     ring.  You may want to do this because another ring has a monomial ordering
     more suitable for the computations you are about to do, or it may have
     additional variables in it, one of which you wish to use for homogenization.
     Here is an example of the latter.  We make another ring with a new variable ", TT "t", "
     in it, transfer the ideal, and then homogenize the ideal.",
     EXAMPLE {
	  "S = ZZ/101[a..d,t];",
      	  "substitute(I,S)",
      	  "homogenize(oo,t)",
	  },
 "In this case, the substitution was done according to the names of
     the variables in the two rings.  There are more explicit ways to specify the
     substitution to be performed.  Here is one where we list the new values for
     all the variables.",
     EXAMPLE {
	  "T = ZZ/101[x,y,z,t];",
	  "use ring I",
      	  "substitute(I,{a=>x^10,b=>y^10,c=>z^10,d=>t^10})",
	  },
     "Now notice that the variable ", TT "a", " appears to be an element of ", TT "S", ".
     The creation of the ring ", TT "S", " supplanted the earlier value.",
     EXAMPLE "a",
     "We restore the variables of ", TT "R", " to visibility.",
     EXAMPLE "use R",
     "To recover the generators of an ideal as a matrix, use ", TO "generators", ".",
     EXAMPLE "generators J",
     "Use the operator ", TT "%", " to reduce a ring element with respect to a
     Groebner basis of the ideal.",
     EXAMPLE "(1+a+a^3+a^4) % J",
     "Membership in the ideal may be tested by comparing the answer to 0 with ", TT "==", ".",
     EXAMPLE {
	  "(1+a+a^3+a^4) % J == 0",
      	  "a^4 % J == 0",
	  },
     PARA{},
     "The usual algebraic operations on ideals are available.",
     EXAMPLE {
	  "I+J",
      	  "intersect(I,J)",
      	  "I*J",
      	  "J:I",
	  "saturate(J,I)",
      	  "radical J",
	  },
     "See also: ", TO "intersect", ", ", TO (symbol :, Ideal, Ideal), ",
     ", TO "saturate", ", and ", TO "MinimalPrimes::radical", ".",
     PARA{},
     "We may ask whether one ideal is contained in another.",
     EXAMPLE {
	  "isSubset(I,J)",
      	  "isSubset(I,I+J)",
      	  "isSubset(I+J,J)",
	  },
     "Once you have an ideal, then you may construct the quotient ring or the quotient
     module (there is a difference).  Here is the quotient ring.",
     EXAMPLE "R/I",
     "Here is the quotient module.",
     EXAMPLE "M = R^1/I",
     "And if you want the module underlying ", TT "I", " itself, you can get it with
     ", TO "module", ".",
     EXAMPLE "module I",
     "In general, when an ideal is used as an argument to a function that usually
     would be given a module, we try to make an informed choice about whether the user
     intends the ideal to be used as a module directly, or whether the quotient module
     is more suitable.  In homological functions such as ", TO "Ext", " and ", TO "Tor", "
     the underlying module is used.  Here are some examples where the quotient 
     module is used.",
     PARA{},
     "A free resolution of ", TT "R^1/I", " can be obtained with ", TO "resolution", ".",
     EXAMPLE "resolution I",
     "The Krull dimension or codimension of the support of the quotient module can
     be obtained.",
     EXAMPLE {
	  "dim I",
      	  "dim J",
      	  "codim I",
	  },
 "(Beware that for a homogeneous ideal the
     dimension of its projective variety is one less than the number provided by
     ", TO "dim", ".)",
     PARA{},
     "If the dimension of the quotient module as a vector space is needed,
     use ", TO "basis", " to get a matrix whose columns form a basis, and compute
     the dimension from it.",
     EXAMPLE {
	  "basis (R^1/J)",
      	  "rank source oo",
	  },
 "(Here ", TO "oo", " refers to the result on the previous line.",
     PARA{},
     "For more information see ", TO "Ideal", "."
     }

document {
     Key => "ideals and modules",
     "In this section we present an overview of ideals and modules.
     For details, see ", TO "Ideal", " and ", TO "Module", ".",
     PARA{},
     "The most general module ", TT "M", " is represented as a submodule of a 
     quotient module of a free module ", TT "F", ".  The quotient module is
     presented internally by a matrix whose columns generate the relations, 
     and the submodule is represented internally by a matrix whose columns
     generate the submodule.  The two matrices the same number of rows, namely,
     the rank of ", TT "F", ".",
     Subnodes => {
	  TO "ideals",
	  TO "free modules",
	  TO "making modules from matrices", -- coker, ker, image, etc.
	  TO "manipulating modules",
	  TO "maps between modules",
	  TO "bases of parts of modules",
	  }
     }
