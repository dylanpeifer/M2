newPackage(
        "DivisionAlgorithm",
        Version => "0.0.0", 
        Date => "January 22, 2020",
        Authors => {{Name => "Dylan Peifer", 
                     Email => "djp282@cornell.edu", 
                     HomePage => "https://www.math.cornell.edu/~djp282"}},
        Headline => "Interface to division algorithm in the engine",
        DebuggingMode => true
        )

export {"divAlg"}

debug Core; -- for rawDivisionAlgorithm

divAlg = method()
divAlg(Matrix, Matrix) := Matrix => (f, g) -> (
    -- f = a matrix over a polynomial ring
    -- g = a matrix over the same ring as f
    -- returns a matrix containing remainders when each column of f is reduced via
    --     polynomial long division by columns of g

    map(target f, source f, rawDivisionAlgorithm(raw f, raw g, 0))
    )

TEST ///
R = ZZ/32003[a..d]
f = vars R
g = matrix {{a*d, b*c}}
assert(divAlg(f, g) - f == 0)
///

TEST ///
R = QQ[x, y]
g = matrix {{(1/2)*x - (1/3)*y}, {3*x - 7*y^2}}
assert(divAlg(g, g) == 0)
///

TEST ///
R = QQ[x]
f = matrix {{(1/2)*x^2 + (1/3)*x + 3}}
g = matrix {{x^10, x^5 + 3, (1/5)*x}}
assert(divAlg(f, g) - matrix {{3_R}} == 0)
///

TEST ///
R = ZZ/32003[x]
f = matrix {{x^5 + 3*x^3 + x^2 + 4}}
g = matrix {{x^2 + 1}}
assert(divAlg(f, g) - matrix{{-2*x + 3}} == 0)
///

end
