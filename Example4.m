Q := Rationals();
prec := 300;
CC := ComplexField(prec);
P<x> := PolynomialRing(Q);

/* Attach CHIMP package to handle superelliptic curves
    THIS SHOULD BE CHANGED TO FIT YOUR INSTALLATION */
AttachSpec("/home/gallo/ConnectedMonodromyField/CHIMP/CHIMP.spec");
QQ := RationalsExtra(prec);


/* ------------------- STEP 0 ----------------------------*/
// Compute the Jacobian's period matrix
SetLogFile("Example4.out");
"Computing period matrix...";

R<t> := PolynomialRing(Q);
f1 := t^7+1/4;
X1 := HyperellipticCurve(f1);
g1 := Genus(X1);
time PP1 := PeriodMatrix(X1);


X2 := EllipticCurve(t^3-t^2-2*t-1, t);
d := -1;
X2 := QuadraticTwist(X2, d);
g2 := Genus(X2);
time PP2 := PeriodMatrix(X2);


g := g1+g2;
assert g eq 4;

// Helper function to combine two matrices as described
function CombineBlocks(P1, P2)
    g1 := NumberOfRows(P1);
    g2 := NumberOfRows(P2);

    // Split each matrix into two square blocks
    A1 := Submatrix(P1, 1, 1, g1, g1);
    B1 := Submatrix(P1, 1, g1 + 1, g1, g1);
    A2 := Submatrix(P2, 1, 1, g2, g2);
    B2 := Submatrix(P2, 1, g2 + 1, g2, g2);

    // Diagonal join of blocks
    A := DiagonalJoin(A1, A2);
    B := DiagonalJoin(B1, B2);

    // Horizontal join final result
    P := HorizontalJoin(A, B);

    return P;
end function;

PP := CombineBlocks(PP1, PP2);


/* ------------------- STEP 1 ----------------------------*/
// Compute the CM algebra E

F := CyclotomicField(7);
G, GAut, toAut := AutomorphismGroup(F);
emb_FC := hom< F -> CC | Roots(ChangeRing(DefiningPolynomial(F), CC))[1][1] >;	

count := 0;
for g in G do
    if g^2 eq Identity(G) and &and[g*h*g^-1*h^-1 eq Identity(G): h in G] and (not (g eq Identity(G))) then
        complex_conjugation_onF := g;
        count +:= 1;
    end if;
end for;
assert count eq 1;

/* -- helper functions -- */
function MinimalInvariantSubspaces(M)
    /* This functions takes a matrix M as input
        and outputs the bases of the subspaces W of V,
        on which M naturally acts,
        corresponding to the irreducible factors
        of its minimal polynomial.
        It's a weaker form of the eigenspace decomposition,
        with spaces defined over the base field of M,
        usually Q. */
    charpoly := P!CharacteristicPolynomial(M);
    factors_charpoly := [ p[1] : p in Factorization(charpoly)];
    
    subspaces := [* *];
    for factor in factors_charpoly do
        eigen0 := Basis(Kernel(Evaluate(factor, M)));
        Append(~subspaces, eigen0);
    end for;

    return subspaces;
end function;

function CommonBlockSpaces(matrices)
    /*  Input:
            -matrices: a list of matrices (with Q coefficients, usually)
        Output:
            - BCM: the basis-change matrix simultaneously block-diagonalising
                all the matrices in the given list
            - subspaces: the list of subspaces W of V (the obvious vector space)
                corresponding to the blocks (we never use this)
            - block_dimensions: the list of dimensions of the blocks in natural order
        This functions takes a list of matrices
        and outputs a simultaneous block-diagonalisation.
    */
    K := BaseRing(matrices[1]);
    V := VectorSpace(K, Nrows(matrices[1]));

    subspaces := [* V *];
    for M in matrices do
        new_bases := MinimalInvariantSubspaces(M);
        new_subs := [ sub< V | basis > : basis in new_bases ];

        subspaces := [* Wold meet Wnew : Wold in subspaces, Wnew in new_subs | Dimension(Wold meet Wnew) ne 0 *];
    end for;

    BCvectors := &cat[ [b : b in Basis(W)] : W in subspaces];
    BCM := Matrix(BCvectors);

    block_dimensions := [ Dimension(W) : W in subspaces];

    return BCM, subspaces, block_dimensions;
end function;

function iota2(x, A)
    /* This functions takes an element x of a number field E=Q<a>
        and a matrix A of any type
        expresses x as a polynomial p(a)
        and gives back p(A). */
    K := Parent(x);
    n := Nrows(A);
    F := BaseRing(A);
    I := IdentityMatrix(F, n);

    // Express x in terms of powers of the generator
    coeffs := Eltseq(x);  // List of coefficients in power basis

    // Evaluate polynomial in A
    X := ZeroMatrix(F, n, n);
    for i in [1..#coeffs] do
        X +:= coeffs[i] * A^(i-1);
    end for;

    return X;
end function;

/* -- helper functions -- */
function AlgebraicMatrix(complex_matrix, closure_CMfield, emb_FC)
    /*  This function takes a matrix *M = complex_matrix* with algebraic coefficients
        in a field *F = closure_CMfield*, but stored as complex numbers.
        The output is the same matrix over F.
    */
    M := complex_matrix;
    entries := Eltseq(M);
    polys := [];
    roots := [];

    F := closure_CMfield;
    K := F;
    emb := emb_FC;

    // Step 1: Get minimal polynomials and matching complex approximations
    for x in entries do
        if IsCoercible(Q, x) then
            Append(~polys, <x, MinimalPolynomial(Q!x), Q!x>);
        else
            px := MinimalPolynomial(x, Degree(F));
            Append(~polys, <x, px, CC!x>); // store complex approx
        end if;
    end for;

    // Step 3: Match the entries
    images := [];
    for tup in polys do
        x_orig, px, x_cmplx := Explode(tup);
        roots := Roots(px, K);
        match := false;
        for rt in roots do
            x_K := K!rt[1]; // lift root to K
            if Abs(emb(x_K) - x_cmplx) lt 1e-8 then
                Append(~images, x_K);
                break;
            end if;
        end for;
    end for;


    // Reconstruct the matrix
    MK := Matrix(K, Nrows(M), Ncols(M), images);
    return MK;

end function;



/* -- CM algebra -- */
// Step 1: compute generators for End^0(J) as a Q algebra
    EndJ, cmplx_gens := EndomorphismRing(PP1);
    EndJ0 := ChangeRing(EndJ, QQ);   

    E1 := F;

// Step 1.5: save generators for later   
    Fgens := [ AlgebraicMatrix(M, F, emb_FC) : M in cmplx_gens ];
    Qgens := [ ChangeRing(A, QQ) : A in Generators(EndJ) ];

    M1 := Fgens[1]^4;
    A1 := Qgens[1];



/* -- CM algebra -- */
// Step 1: compute generators for End^0(J) as a Q algebra
    EndJ, cmplx_gens := EndomorphismRing(PP2);
    EndJ0 := ChangeRing(EndJ, QQ);

    Fgens := [ AlgebraicMatrix(M, F, emb_FC) : M in cmplx_gens ];
    Qgens := [ ChangeRing(A, QQ) : A in Generators(EndJ) ];

    A2 := Qgens[1];
    M2 := Matrix(F, 1, 1 , [Roots(MinimalPolynomial(A2), F)[1,1]] );

    MonogenicGenerator := A2;
    mu := P!MinimalPolynomial(MonogenicGenerator);
    EE := NumberField(mu);
    E2 := EE;
    assert IsSubfield(E2, F);
    assert F!E2.1 eq M2[1,1];

"------------------";
"STEP 1 OK!";
"------------------";
/* ------------------- STEP 2 ----------------------------*/
// Compute the CM type

"Computing CM type...";
function BlockDiagonalMatrix(matrices)
    /* Given a list of diagonal matrices,
        reutrns their diagonal join */
    B := matrices[1];
    for i in [2..#matrices] do
        B := DiagonalJoin(B, matrices[i]);
    end for;
    return B;
end function;
CM_types := [* *];

D := BlockDiagonalMatrix([* M1, M2 *]);
diagonalized_complex := [*M1, M2*];
BCM_cmplx := IdentityMatrix(QQ, 4);

CM_type := [* hom< E1 -> F | D[i,i] > : i in [1..3] | D[i,i] ne 0 *];
Append(~CM_types, CM_type);
CM_type := [* hom< E2 -> F | D[i,i] > : i in [4..4] | D[i,i] ne 0 *];
Append(~CM_types, CM_type);



iotaE := [*[E1], [E2]*];





"------------------";
"STEP 2 OK!";
"------------------";
/* ------------------- STEP 3 ----------------------------*/
// Compute MT equations


/* -- helper functions -- */
function FieldHom(E, F)
    /* Takes two field E in F,
        such that E is a subfield of F
        and return the list of all embeddings E -> F */
    assert IsSubfield(E, F);
    f := DefiningPolynomial(E);
    roots := Roots(f, F);  // Each root is a pair <α, mult>
    conjugates := [r[1] : r in roots];
    homEF := [* hom< E -> F | c > : c in conjugates *];
    assert #homEF eq Degree(E);
    return homEF;
end function;

function FindGaloisAutomorphism(sigma, E)
    /*
        Helper function:
            given an embedding sigma: E -> F,
            computes an element g in Gal(F/Q)
            that restricts to sigma on E
            (as an automorphism of F).
    */
    for g in G do
        auto := toAut(g);
        if auto(E.1) eq sigma(E.1) then
            return auto;
        end if;
    end for;
    error "No matching Galois automorphism found for phi";
end function;

function BlockDiagonalMatrix(matrices)
    /* Given a list of diagonal matrices,
        reutrns their diagonal join */
    B := matrices[1];
    for i in [2..#matrices] do
        B := DiagonalJoin(B, matrices[i]);
    end for;
    return B;
end function;

function HorizontalJoinList(matrices)
    /* Given a list of diagonal matrices,
        reutrns their horizontal join */
    M := matrices[1];
    for i in [2..#matrices] do
        M := HorizontalJoin(M, matrices[i]);
    end for;
    return M;
end function;

c := toAut(complex_conjugation_onF);
homE1F := CM_types[1] cat [* hom< E1->F | c(ff(E1.1)) > : ff in CM_types[1] *];
homE2F := CM_types[2] cat [* hom< E2->F | c(ff(E2.1)) > : ff in CM_types[2] *];


    CM_type := CM_types[1];
    E := E1;
    Estar := E1;
    sigmas := homE1F;
    etas := homE1F;

    // Compute CM lift
    CM_lift := [];
    for g in G do
        auto := toAut(g);
        if &or[auto(E.1) eq sigma(E.1) : sigma in CM_type] then
            Append(~CM_lift, g);
        end if;
    end for;

    CM_tilde := [ g^-1 : g in CM_lift ];
    CM_star := [ ];
    for g in CM_tilde do
        already_represented := &or[ toAut(g)(Estar.1) eq toAut(h)(Estar.1) : h in CM_star ];
        if not already_represented then
            Append(~CM_star, g);
        end if;
    end for;

    // Table: embedding ↔ g ∈ Gal(F/Q)
    embeddingToAuto := AssociativeArray();
    for sigma in sigmas do
        embeddingToAuto[sigma] := FindGaloisAutomorphism(sigma, E);
    end for;

    // Initialize the matrix M: rows = |etas|, cols = |sigmas|
    M := ZeroMatrix(Integers(), #etas, #sigmas);

    for j in [1..#sigmas] do
        sigma := sigmas[j];
        g_sigma := embeddingToAuto[sigma];

        for g_phi in CM_star do
            g := toAut(g_phi) * g_sigma;
            eta := hom< Estar -> F | g(Estar.1) >;

            // Match eta with one of the standard etas (up to equality on powers)
            for i in [1..#etas] do
                eta_std := etas[i];
                if &and[eta(Estar.1^k) eq eta_std(Estar.1^k) : k in [1..Degree(Estar)]] then
                    M[i][j] +:= 1;
                    break;
                end if;
            end for;
        end for;
    end for;

    reflex_matrix1 := M;



    CM_type := CM_types[2];
    E := E2;
    Estar := E2;
    sigmas := homE2F;
    etas := homE2F;

    // Compute CM lift
    CM_lift := [];
    for g in G do
        auto := toAut(g);
        if &or[auto(E.1) eq sigma(E.1) : sigma in CM_type] then
            Append(~CM_lift, g);
        end if;
    end for;

    CM_tilde := [ g^-1 : g in CM_lift ];
    CM_star := [ ];
    for g in CM_tilde do
        already_represented := &or[ toAut(g)(Estar.1) eq toAut(h)(Estar.1) : h in CM_star ];
        if not already_represented then
            Append(~CM_star, g);
        end if;
    end for;

    // Table: embedding ↔ g ∈ Gal(F/Q)
    embeddingToAuto := AssociativeArray();
    for sigma in sigmas do
        embeddingToAuto[sigma] := FindGaloisAutomorphism(sigma, E);
    end for;

    // Initialize the matrix M: rows = |etas|, cols = |sigmas|
    M := ZeroMatrix(Integers(), #etas, #sigmas);

    for j in [1..#sigmas] do
        sigma := sigmas[j];
        g_sigma := embeddingToAuto[sigma];

        for g_phi in CM_star do
            g := toAut(g_phi) * g_sigma;
            eta := hom< Estar -> F | g(Estar.1) >;

            // Match eta with one of the standard etas (up to equality on powers)
            for i in [1..#etas] do
                eta_std := etas[i];
                if &and[eta(Estar.1^k) eq eta_std(Estar.1^k) : k in [1..Degree(Estar)]] then
                    M[i][j] +:= 1;
                    break;
                end if;
            end for;
        end for;
    end for;

    reflex_matrix2 := M;

reflex_matrix := BlockDiagonalMatrix([*reflex_matrix1, reflex_matrix2*]);

/*
"Computing reflex norm matrix...";
// Diagonal join of reflex norm matrices of blocks
reflex_matrix := [* *];
for i in [1..#iotaE] do
    E := iotaE[i, 1];
    CM_type := CM_types[i];
    ReflexNorm := ReflexNormMatrix(E, CM_type);
    Append(~reflex_matrix, ReflexNorm);
end for;
reflex_matrix := BlockDiagonalMatrix(reflex_matrix);

reflex_matrix_1 := Matrix(Integers(), [
    [1,1,1,0,0,0],
    [0,1,0,1,0,1],
    [0,1,1,0,0,1],
    [1,0,0,1,1,0],
    [1,0,1,0,1,0],
    [0,0,0,1,1,1]
]);

reflex_matrix := BlockDiagonalMatrix([*reflex_matrix_1, IdentityMatrix(Integers(), 2)*]);
*/

/* -- norm matrix -- */
/* Given a field E (subfield of F)
        computes the norm matrix Z[Hom(F,F)]-> Z[Hom(E,F)] */

    // Step 1: Get all embeddings E -> F
    sigmas := homE1F;
    E := E1;
    Estar := E1;
    autos := [ g : g in G, i in [1..#homE1F] | toAut(g)(E1.1) eq homE1F[i](E1.1) ];
    etas := [ toAut(g) : g in autos ];
    
    norm_autos := [ g : g in autos | toAut(g)(Estar.1) eq Estar.1 ];

    // Table: embedding ↔ g ∈ Gal(F/Q)
    embeddingToAuto := AssociativeArray();
    for sigma in sigmas do
        embeddingToAuto[sigma] := FindGaloisAutomorphism(sigma, Estar);
    end for;

    // Initialize the matrix M: rows = |etas|, cols = |sigmas|
    M := ZeroMatrix(Integers(), #etas, #sigmas);

    for j in [1..#sigmas] do
        sigma := sigmas[j];
        g_sigma := embeddingToAuto[sigma];

        for phhi in norm_autos do
            g_phi := toAut(phhi);
            eta := g_phi*g_sigma;

            // Match eta with one of the standard etas (up to equality on powers)
            for i in [1..#etas] do
                eta_std := etas[i];
                if &and[eta(F.1^k) eq eta_std(F.1^k) : k in [1..Degree(F)]] then
                    M[i][j] +:= 1;
                    break;
                end if;
            end for;
        end for;
    end for;

norm_matrix1 := M;

    // Step 1: Get all embeddings E -> F
    sigmas := homE2F;
    E := E2;
    Estar := E2;
    norm_autos := [ g : g in autos | toAut(g)(Estar.1) eq Estar.1 ];

    // Table: embedding ↔ g ∈ Gal(F/Q)
    embeddingToAuto := AssociativeArray();
    for sigma in sigmas do
        embeddingToAuto[sigma] := FindGaloisAutomorphism(sigma, Estar);
    end for;

    // Initialize the matrix M: rows = |etas|, cols = |sigmas|
    M := ZeroMatrix(Integers(), #etas, #sigmas);

    for j in [1..#sigmas] do
        sigma := sigmas[j];
        g_sigma := embeddingToAuto[sigma];

        for phhi in norm_autos do
            g_phi := toAut(phhi);
            eta := g_phi*g_sigma;

            // Match eta with one of the standard etas (up to equality on powers)
            for i in [1..#etas] do
                eta_std := etas[i];
                if &and[eta(F.1^k) eq eta_std(F.1^k) : k in [1..Degree(F)]] then
                    M[i][j] +:= 1;
                    break;
                end if;
            end for;
        end for;
    end for;

norm_matrix2 := M;

norm_matrix := HorizontalJoinList([* norm_matrix1, norm_matrix2 *]);


/*
aaa := Matrix(Integers(), [
    [1,0],
    [1,0],
    [0,1],
    [1,0],
    [0,1],
    [0,1]
]);
norm_matrix := HorizontalJoin([IdentityMatrix(Integers(), 6), aaa]);
*/

/* -- MT equations -- */
"Computing equations for MT group...";
MTequations := Basis(Kernel(Transpose(norm_matrix*reflex_matrix)));
MTequations;








"------------------";
"STEP 3 OK!";
"------------------";

/* ------------------- STEP 4 ----------------------------*/
// Compute the periods!


function MTequation_to_IndexTuple(f)
    tuple := [];
    for i in [1..3] do
        if f[i] ge 0 then
            tuple := tuple cat [ i : j in [1..f[i]]];
        else 
            tuple := tuple cat [ i+3 : j in [1..-f[i]]];
        end if;
    end for;

    for i in [7..7] do
        if f[i] ge 0 then
            tuple := tuple cat [ i : j in [1..f[i]]];
        else 
            tuple := tuple cat [ i+1 : j in [1..-f[i]]];
        end if;
    end for;
    
    for i in [4..6] do
        if f[i] ge 0 then
            tuple := tuple cat [ i : j in [1..f[i]]];
        else 
            tuple := tuple cat [ i-3 : j in [1..-f[i]]];
        end if;
    end for;

    for i in [8..8] do
        if f[i] ge 0 then
            tuple := tuple cat [ i : j in [1..f[i]]];
        else 
            tuple := tuple cat [ i-1 : j in [1..-f[i]]];
        end if;
    end for;

    return tuple;
end function;

FF := NumberFieldExtra(DefiningPolynomial(F));
pp := (2*Pi(CC)*CC.1);
ee := [ PP[1,1], PP[2,1], PP[3,1], pp/PP[1,1], pp/PP[2,1], pp/PP[3,1], PP[4,4], pp/PP[4,4] ];

putative_Kconn := NumberFieldExtra(ChangeRing(x^2-d, FF));

for f in MTequations do
    If := MTequation_to_IndexTuple(f);
    period := &*[ ee[j]: j in If ]/(2*Pi(CC)*CC.1)^2;
    pf1 := MinimalPolynomialExtra(period, FF);
    if Degree(pf1) gt 1 then
        period;
        Kconn := NumberFieldExtra(pf1);
        Kconn;
        assert IsIsomorphic(Kconn, putative_Kconn); 
    end if;
end for;
    
