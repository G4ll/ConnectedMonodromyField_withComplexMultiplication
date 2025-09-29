Q := Rationals();
CC := ComplexField(500);
P<x> := PolynomialRing(Q);

/* Attach CHIMP package to handle superelliptic curves
    THIS SHOULD BE CHANGED TO FIT YOUR INSTALLATION
*/
AttachSpec("/home/gallo/ConnectedMonodromyField/CHIMP/CHIMP.spec");
QQ := RationalsExtra(500);
R<x,y> := PolynomialRing(QQ,2);

/* Pick your favourite degenerate CM superelliptic curve:
    this file cannot handle CM-algebras with isomorphic factors. */
f := x^4-x^5-y^12;
r := 1;
f := x^2*(x^2-1)^(2*r)*(x^2+1)^(2*r^2)-y^7;
//f1 := x^9+1-y^2;
//f2 := x^15+1-y^2;
//f5 := x^9 -2*x^8 - 8*x^7 + 16*x^6 + 20*x^5 - 40*x^4 - 16*x^3 + 32*x^2 + 2*x - 4 - y^2;


/* ------------------- STEP 0 ----------------------------*/
// Compute the Jacobian's period matrix
SetLogFile("Example2_test1.out");
"Computing period matrix...";
X := Curve(AffineSpace(R), f);
Xproj := ProjectiveClosure(X);
g := Genus(Xproj);
PP := PeriodMatrix(Xproj);


/* ------------------- STEP 1 ----------------------------*/
// Compute the CM algebra E




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



/* -- CM algebra -- */
function ComputeCMAlgebra(PP)
    /* This function takes the big period matrix PP as imput
        and outputs generators for the étale alegbra E
        that is the center of End^0(J).
        We are assuming that E = E_1 x ... x E_r
        where the E_i are **distinct** separable fields.
        
        Output:
            -fields: this is a list of 3-uples (E_i, M1, M2) where
                ~ E_i = Q(a_i) is the i-th field in the decomposition of E
                ~ M1 is an matrix in the rational representation of EndJ0
                    corresponding to iota(0,..,a_i,...,0)
                ~ M2 is the matrix corresponding to M1 in the i-th block
                    after simultaneous block-diagonalisation (sbd)
            -blocks: list of generators for the rational rep of EndJ0
                reduced to each block after sbd
            -BCM: the sbd basis-change matrix
        */

    // Step 1: compute generators for End^0(J) as a Q algebra
    EndJ, cmplx_gens := EndomorphismRing(PP);
    EndJ0 := ChangeRing(EndJ, Q);

    // Step 2: compute the center iotaE
    iotaE := Center(EndJ0);
    iotaE_gens := [ g : g in Generators(iotaE)];

    // Step 3: recognize the block decomposition into simple algebras
    BCM, _, block_dimensions := CommonBlockSpaces(iotaE_gens);
    iotaE_gens_block := [ BCM*g*BCM^-1 : g in iotaE_gens];

    // Step 4: get generators for the simple algebras
    blocks := [* *];
    block_starting_index := 1;
    for index in [1..#block_dimensions] do
        I := [block_starting_index..block_starting_index+block_dimensions[index]-1];
        block_generators := [ Submatrix(g, I, I) : g in iotaE_gens_block ];
        Append(~blocks, block_generators);
        block_starting_index := block_starting_index + block_dimensions[index];
    end for;

    algebras := [* *];
    for block in blocks do
        block_algebra := MatrixAlgebra< Q, Nrows(block[1]) | block >;
        Append(~algebras, block_algebra);
    end for;

    // Step 5: recognize each simple component as a field Ei and appoint a generator iota(Ei.1)
    fields := [* *];
    block_starting_index := 1;
    for block in blocks do
        E := Q;
        for a in block do
            // This will break
            mu_a := MinimalPolynomial(a);
            //mu_a := PolynomialRing(E)!MinimalPolynomial(ChangeRing(a, E));
            //max_degree := Max([ mu_factor[2] : mu_factor in Factorization(mu_a)]);
            //mu_a := [ mu_factor[1] : mu_factor in Factorization(mu_a) | mu_factor[2] eq max_degree ][1];
            Ka := NumberField(mu_a);
            E := Compositum(E, Ka);
        end for;
        E, _ := OptimizedRepresentation(E);

        MonogenicGenerator := &+[ i * block[i] : i in [1..#block]];
        mu := P!MinimalPolynomial(MonogenicGenerator);
        EE := NumberField(mu);
        check, EtoEE := IsIsomorphic(E, EE);
        assert check;

        iotaE1 := iota2(EtoEE(E.1), MonogenicGenerator);

        iotaE1_big := ZeroMatrix(Q, Nrows(iotaE_gens[1]));
        InsertBlock(~iotaE1_big, iotaE1, block_starting_index, block_starting_index);
        iotaE1_big := BCM^-1*iotaE1_big*BCM;

        Append(~fields, <E, iotaE1_big, iotaE1>);
    end for;

    return fields, blocks, BCM;
end function;

"Computing CM field...";
iotaE, iotaE_blocks, BCM := ComputeCMAlgebra(PP);


// Define F as the compositum of the Galois closure of all E_i in E = E_1 x ... x E_t
F := Q;
for tuple in iotaE do
    F := Compositum(F, NormalClosure(tuple[1]));
end for;
F<z>, _ := OptimizedRepresentation(F);
"The Galois closure F is the", F;

// Save the Galois group of F/Q and fix an embedding F --> C
G, GAut, toAut := AutomorphismGroup(F);
emb_FC := hom< F -> CC | Roots(ChangeRing(DefiningPolynomial(F), CC))[1][1] >;	




"------------------";
"STEP 1 OK!";
"------------------";
/* ------------------- STEP 2 ----------------------------*/
// Compute the CM type



/* -- helper functions -- */
function AlgebraicMatrix(complex_matrix, closure_CMfield)
    /*  This function takes a matrix *M = complex_matrix* with algebraic coefficients
        in a field *F = closure_CMfield*, but stored as complex numbers.
        The output is the same matrix over F.
    */
    M := complex_matrix;
    entries := Eltseq(M);
    polys := [];
    roots := [];

    F := closure_CMfield;

    // Step 1: Get minimal polynomials and matching complex approximations
    for x in entries do
        if IsCoercible(Q, x) then
            Append(~polys, <x, MinimalPolynomial(Q!x), Q!x>);
        else
            px := MinimalPolynomial(x, Degree(F));
            Append(~polys, <x, px, CC!x>); // store complex approx
        end if;
    end for;

    /*
    // Step 2: Build compositum of all minimal polynomials
    fields := [];
    for tup in polys do
        _, px, _ := Explode(tup);
        Append(~fields, NumberField(px : DoLinearExtension := true));
    end for;

    if #fields eq 0 then
        return Q, M;
    end if;

    K := fields[1];
    for i in [2..#fields] do
        K := Compositum(K, fields[i]);
    end for;
    
    // Blah
    assert IsSubfield(K, F);
    */
    K := F;
    K, _ := OptimizedRepresentation(K);
    emb := hom< K -> CC | Roots(ChangeRing(DefiningPolynomial(K), CC))[1,1]>;

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




/* -- CM type -- */
function ComputeCMtype(PP)
        /* This function takes the big period matrix PP as imput
        and outputs generators for the étale alegbra E
        that is the center of End^0(J).
        We are assuming that E = E_1 x ... x E_r
        where the E_i are **distinct** separable fields.
        Gives generators both for the rational rep and the tangent rep.
        
        Output:
            -fields: this is a list of 3-uples (E_i, A_i, M_i) where
                ~ E_i = Q(a_i) is the i-th field in the decomposition of E
                ~ A_i is the Q-matrix in the rational representation of EndJ0
                    corresponding to iota(0,..,a_i,...,0)
                ~ M_i is the F-matrix in the *tanget* representation of EndJ0
                    corresponding to iota(0,..,a_i,...,0)
            -blocks: list of generators for the rational rep of EndJ0
                reduced to each block after sbd
            -BCM: the simultaneous-block-diagonalisation basis-change matrix
        */

    // Step 1: compute generators for End^0(J) as a Q algebra
    EndJ, cmplx_gens := EndomorphismRing(PP);
    Fgens := [ AlgebraicMatrix(M, F) : M in cmplx_gens ];
    Qgens := [ ChangeRing(A, Q) : A in Generators(EndJ) ];
    
    /*
    // Step 2: compute the center iotaE
    iotaE := Center(EndJ);
    iotaE_gens := [ g : g in Generators(iotaE)];
    */

    // Step 3: recognize the block decomposition into simple algebras
    BCM, _, block_dimensions := CommonBlockSpaces(Qgens);
    iotaE_gens_block := [ BCM*g*BCM^-1 : g in Qgens];

    // Step 4: get generators for the simple algebras
    blocks := [* *];
    block_starting_index := 1;
    for index in [1..#block_dimensions] do
        I := [block_starting_index..block_starting_index+block_dimensions[index]-1];
        block_generators := [ Submatrix(g, I, I) : g in iotaE_gens_block ];
        Append(~blocks, block_generators);
        block_starting_index := block_starting_index + block_dimensions[index];
    end for;

    /*
    algebras := [* *];
    for block in blocks do
        block_algebra := MatrixAlgebra< Q, Nrows(block[1]) | block >;
        Append(~algebras, block_algebra);
    end for;
    */

    // Step 5: recognize each simple component as a field Ei and appoint a generator iota(Ei.1)
    fields := [* *];
    block_starting_index := 1;
    for block in blocks do
        // Step 5.1: recognize the field E1 (might need adjustment if not Galois)
        E := Q;
        for a in block do
            mu_a := P!MinimalPolynomial(a);
            Ka := NumberField(mu_a);
            E := Compositum(E, Ka);
        end for;
        E<a>, _ := OptimizedRepresentation(E);
        
        /* Step 5.2: find monogenic generator MG in EndJ0/Z such that, if E1 = Q(alpha),
            then iota(alpha) = MG */
        MonogenicGenerator := &+[ i * block[i] : i in [1..#block]];
        mu := P!MinimalPolynomial(MonogenicGenerator);
        EE, _ := NumberField(mu);
        check, EtoEE := IsIsomorphic(E, EE);
        assert check;

        iotaE1 := iota2(EtoEE(E.1), MonogenicGenerator);

        iotaE1_big := ZeroMatrix(Q, Nrows(Qgens[1]));
        InsertBlock(~iotaE1_big, iotaE1, block_starting_index, block_starting_index);
        iotaE1_big := BCM^-1*iotaE1_big*BCM;
        block_starting_index := block_starting_index + Nrows(block[1]);

        // Step 5.4: reconstruct complex monogenic generator for the E1 factor
        target := ChangeRing(PP, CC)*ChangeRing(iotaE1_big, CC);
        target := Submatrix(target, [1..Nrows(PP)], [1..Nrows(PP)]);
        Ma := target*Submatrix(ChangeRing(PP, CC), [1..Nrows(PP)], [1..Nrows(PP)])^-1;
        Ma := AlgebraicMatrix(Ma, F);

        //EndJ0 := ChangeRing(EndJ, Q);
        //EndJ_alg := MatrixAlgebra< F, Nrows(Fgens[1]) | [MatrixAlgebra(F, Nrows(Fgens[1]))!f : f in Fgens] >;
        //hom< EndJ0 -> EndJ_alg | [EndJ_alg!f : f in Fgens] >;

        Append(~fields, <E, iotaE1_big, Ma>);
    end for;

    return fields, blocks, BCM;
end function;

"Computing CM type...";
iotaE, iotaE_blocks, _ := ComputeCMtype(PP);


/* This is the actual CM type computation:
    once we have F-generatos M_i for the fields E_i,
    we take a simultanous diagonalisation
    and look at the diagonal entries!

    In the following, we will use
        - diagonalized_complex: the list of generators M_i over F diagonalized
        - BCM_cmplx: the complex matrix simultanously diagonalising all matrices M_i
        - CM_types: the list of CM types divied into blocks [ [CM-types for E1], ... ]
            the CM-types are ordered as they appear in diagonalized_complex[i].
*/
CM_types := [* *];
diagonalized_complex, BCM_cmplx := Diagonalisation([data[3]: data in iotaE]);
block_starting_index := 1;
for data in iotaE do
    E := data[1];
    D := BCM_cmplx * data[3] * BCM_cmplx^-1;
    CM_type := [ hom< E -> F | F!D[i,i] > : i in [1..Nrows(D)] | D[i,i] ne 0];

    Append(~CM_types, CM_type);
end for;
CM_types;









"------------------";
"STEP 2 OK!";
"------------------";
/* ------------------- STEP 3 ----------------------------*/
// Compute MT equations


/* -- helper functions -- */
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



/* -- reflex field -- */
function ReflexField(E, CM_type)
    /* Given a field E (subfield of F) and its CM-type
        computes the reflex field E* */
    //F := GaloisClosure(E);
    autos := [g : g in G];

    // All embeddings E -> F, here F is the globally defined Galois closure
    homEF := FieldHom(E, F);

    // Compute CM lift
    CM_lift := [];
    for g in autos do
        auto := toAut(g);
        if &or[F!auto(F!E.1) eq F!sigma(E.1) : sigma in CM_type] then
            Append(~CM_lift, g);
        end if;
    end for;

    Hstar_gen := [ g : g in G | &and[ g * h in CM_lift: h in CM_lift ] ];

    // Subgroup of G that fixes the inverse orbit
    Hstar := sub< G | Hstar_gen >;

    // Reflex field = fixed field of H
    EStar := FixedField(F, [toAut(h) : h in Hstar]);

    return EStar;
end function;

"Computing reflex field...";
reflex_fields := [* *];
for i in [1..#iotaE] do
    E := iotaE[i, 1];
    CM_type := CM_types[i];
    Estar := ReflexField(E, CM_type);
    Append(~reflex_fields, Estar);
end for;



/* -- reflex norm matrix -- */
function ReflexNormMatrix(E, CM_type)
    /* Given a field E (subfield of F) and its CM-type
        computes the reflex norma matrix Z[Hom(E*,F)]-> Z[Hom(E,F)] */

    // Compute reflex field E* as the field generated by the traces Tr_Phi(x)
    Estar := ReflexField(E, CM_type);
    
    // Get all embeddings
    sigmas := FieldHom(E, F);
    etas := FieldHom(Estar, F);

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

        for phhi in CM_type do
            g_phi := embeddingToAuto[phhi];
            g := g_sigma * g_phi^-1;
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

    return M;
end function;

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



/* -- norm matrix -- */
function EmbeddingToAutomorphismMatrix(Estar, F)
    /* Given a field E (subfield of F)
        computes the norm matrix Z[Hom(F,F)]-> Z[Hom(E,F)] */

    // Step 1: Get all embeddings E -> F
    sigmas := FieldHom(Estar, F);
    etas := FieldHom(F, F);
    autos := [ g : g in G ];
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
            eta := g_sigma * g_phi;

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

    return M;
end function;

"Computing norm matrix...";
norm_matrix := [* *];
// Horizontal join of norm matrices of extensions F/E_i*
for i in [1..#iotaE] do
    Estar := reflex_fields[i];
    NormMatrix := EmbeddingToAutomorphismMatrix(Estar, F);
    Append(~norm_matrix, NormMatrix);
end for;
norm_matrix := HorizontalJoinList(norm_matrix);



/* -- MT equations -- */
"Computing equations for MT group...";
MTequations := Basis(Kernel(Transpose(norm_matrix*reflex_matrix)));
MTequations;








"------------------";
"STEP 3 OK!";
"------------------";
/* ------------------- STEP 4 ----------------------------*/
// Compute the periods!



/* -- helper functions -- */
function SmallConjugationBijection(E, i)
    homEF := FieldHom(E,F);
    sigma := homEF[i];
    sigmabar_E1 := ComplexConjugate(emb_FC(sigma(E.1)));
    
    for j in [1..#homEF] do
        scarto := sigmabar_E1 - emb_FC(homEF[j](E.1));
        if Norm(scarto) lt 10^-9 then
            return j;
        end if;
    end for;

    "Argh!";
end function;

function WhichBlock(CM_types, sigma_index)
    CM_numbers := [ 2*#CMt : CMt in CM_types ];
    CM_sums := [ &+[ CM_numbers[j] : j in [1..i] ] : i in [1..#CM_numbers] ];
    
    assert sigma_index le CM_sums[#CM_sums];
    
    adjust := 0;
    
    for index in [1..#CM_sums] do
        if sigma_index le CM_sums[index] then
            return index, adjust;
        end if;
        adjust := CM_sums[index];
    end for;
end function;

function BigConjugationBijection(CM_types, i)
    block_index, adjust := WhichBlock(CM_types, i);
    E := iotaE[block_index, 1];
    
    j := SmallConjugationBijection(E, i-adjust);
    return j+adjust;
end function;

function BuildIndexTuple(MTequation, CM_types)
    f := MTequation;
    IndexTuple := [];
    
    for i in [1..Ncols(f)] do
        if f[i] ge 0 then
            IndexTuple := IndexTuple cat [ i : j in [1..f[i]]];
        else
            IndexTuple := IndexTuple cat [ BigConjugationBijection(CM_types, i) : j in [1..Integers()!Abs(f[i])]];
        end if;
    end for;

    return IndexTuple;
end function;

function ApplyEmbeddingToMatrix(M, ii)
    F := BaseRing(M);
    K := Codomain(ii);
    m := Nrows(M);
    n := Ncols(M);
    
    N := ZeroMatrix(K, m, n);
    for i in [1..m] do
        for j in [1..n] do
            N[i][j] := ii(M[i][j]);
        end for;
    end for;

    return N;
end function;

function SmallIndexBijection(E, CM_type, sigma_index)
    homEF := FieldHom(E, F);
    sigma := homEF[sigma_index];

    for j in [1..#CM_type] do
        if sigma eq CM_type[j] then
            return j, false;
        end if;
    end for;

    // Returns true if we need to take the complex conjugate
    sigma := homEF[SmallConjugationBijection(E, sigma_index)];
    for j in [1..#CM_type] do
        if sigma eq CM_type[j] then
            return j, true;
        end if;
    end for;
end function;

function BlockPoistionAdjustment(diagonalized_complex, block_index)
    D := diagonalized_complex[block_index];   
    return [ i : i in [1..Nrows(D)] | D[i,i] ne 0];
end function;

function BigIndexBijection(CM_types, sigma_index, diagonalized_complex)
    block_index, adjust := WhichBlock(CM_types, sigma_index);
    E := iotaE[block_index, 1];
    CM_type := CM_types[block_index];

    jj, boo := SmallIndexBijection(E, CM_type, sigma_index - adjust);
    adj2 := BlockPoistionAdjustment(diagonalized_complex, block_index);
    return adj2[jj], boo;
end function;





/* -- compute periods -- */
function ComputePeriod(PP, MTequation, CM_types, diagonalized_complex)
    /*  Input:
            - PP: the big period matrix
            - MTequaion: an equation for the MT group,
                it is a Laurent monomial given as the list of exponents
            - CM_types: the list of CM types defined above
            - diagonalized_complex: the basis-change matrix used to
                diagonalize the Mi and compute the CM-type
        
        Output: the minimal polynomial of the period
            associated to f using the (2 pi i) conjugation trick
    */

    // Pick an arbitrary cycle sigma: 
    cycle_index := 1;

    // Compute the index tuple I_f:
    If := BuildIndexTuple(MTequation, CM_types);
    n := Integers()!(#If/2);

    // Basis-change of the big period matrix:
    PP := ChangeRing(PP, CC);
    elementary_period := ApplyEmbeddingToMatrix(BCM_cmplx, emb_FC)*PP;

    period := CC!1;
    for sigma_index in If do
        // Recognize which omega_j correspond to x_i
        j, needtoconj := BigIndexBijection(CM_types, sigma_index, diagonalized_complex);
        new_factor := elementary_period[j,cycle_index];
        
        // if j > g we use a trick to compute the integral
        if needtoconj then
            new_factor := (2*Pi(CC)*CC.1)/(new_factor);
        end if;

        period := period * new_factor;
    end for;

    period := period / (2*Pi(CC)*CC.1)^n;

    return P!MinimalPolynomial(period, 20);
end function;


"Computing periods...";

Kconn := F;
for f in MTequations do
    pf := ComputePeriod(PP, f, CM_types, diagonalized_complex);
    Kpf, _ := OptimizedRepresentation(SplittingField(pf));
    if not IsSubfield(Kpf, Kconn) then
        Kconn := Compositum(Kconn, Kpf);
        Kconn, _ := OptimizedRepresentation(Kconn);
        "Ding!";
    end if;
end for;

"------------------";
"COMPUTATION SUCCESSFUL!";
"------------------";

"K(e_J) is", Kconn;
"Is the variety nondegenerate?", IsSubfield(Kconn, F);
