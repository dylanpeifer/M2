newPackage(
        "DivisionAlgorithm",
        Version => "0.0.0", 
        Date => "March 22, 2020",
        Authors => {{Name => "Dylan Peifer", 
                     Email => "djp282@cornell.edu", 
                     HomePage => "https://www.math.cornell.edu/~djp282"}},
        Headline => "Interface to division algorithm in the engine",
        DebuggingMode => true
        )

export {"divAlg", "divAlgWithStats"}

debug Core; -- for rawDivisionAlgorithm

divAlg = method()
divAlg(Matrix, Matrix) := Matrix => (f, g) -> (
    -- f = a matrix over a polynomial ring
    -- g = a matrix over the same ring as f
    -- returns a matrix containing remainders when each column of f is reduced via
    --     polynomial long division by columns of g

    first divAlgWithStats(f, g)
    )

divAlgWithStats = method()
divAlgWithStats(Matrix, Matrix) := Sequence => (f, g) -> (
    (mat, stats) := rawDivisionAlgorithm(raw f, raw g, 0);
    (map(target f, source f, mat), stats)
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

TEST ///
R = ZZ/32003[x]
f = matrix {{x^5 + 3*x^3 + x^2 + 4}}
g = matrix {{x^2 + 1}}
(mat, stats) = divAlgWithStats(f, g)
assert(mat - matrix{{-2*x + 3}} == 0)

///

end

restart
needsPackage "DivisionAlgorithm"
check DivisionAlgorithm


reduceOverField = method()
reduceOverField(Matrix) := M -> (
    if M == 0 then return M;
    mons := reverse flatten entries monomials M;
    m := gens gb last coefficients(M, Monomials => mons);
    (matrix {mons}) * m
    )

spairs = method()
spairs(Matrix) := G -> (
    G * (syz leadTerm G)
    )

newGroebner = method()
newGroebner(Matrix) := M -> (
    G := reduceOverField M;
    while (
      sp := spairs G;
      g := reduceOverField elapsedTime divAlg(sp, G);
      g != 0) do (
      G = G | g;
      << numcols G << endl;
    );
    G
    )


R = QQ[a..e]
F = for i from 1 to 4 list random(3, R, Height => 10)
M = matrix {F}
elapsedTime newGroebner M;
elapsedTime gens gb M;
M = matrix entries M
elapsedTime groebnerBasis(M, Strategy => "F4");


G2 = reduceOverField M;
S3 = spairs(G2);
G3 = reduceOverField divAlg(S3, G2);
G3 = G2 | G3;
S4 = spairs G3;
G4 = reduceOverField divAlg(S4, G3);
G4 = G3 | G4;
S5 = spairs G4;
G5 = reduceOverField divAlg(S5, G4);
G5 = G4 | G5;
S6 = spairs G5;
G6 = reduceOverField divAlg(S6, G5);
G6 = G5 | G6;


G2 = gens gb(M, DegreeLimit => 2)
S3 = G2 * (syz leadTerm G2)
M3 = divAlg(S3, G2)
G3 = gens gb(M3, DegreeLimit => 3)
G = G2 | G3
S4 = G * (syz leadTerm G)
M4 = divAlg(S4, G)

