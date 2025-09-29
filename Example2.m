Q := Rationals();
prec := 5000;
CC := ComplexField(prec);
P<x> := PolynomialRing(Q);

/* Attach CHIMP package to handle superelliptic curves
    THIS SHOULD BE CHANGED TO FIT YOUR INSTALLATION
*/
AttachSpec("/home/gallo/ConnectedMonodromyField/CHIMP/CHIMP.spec");
QQ := RationalsExtra(prec);
R0<t> := PolynomialRing(QQ);
KK<mu> := NumberFieldExtra(t^3 - t^2 - 2*t + 1);
R<x> := PolynomialRing(KK);
f := 1/9625883310912944*(5609411386822656*mu^2 - 22655110984547328*mu + 2322306677186327)*x^10 - 567/64*x^9 + 1/2406470827728236*(-66261172006842624*mu^2 + 267613498504965312*mu - 219310695028907055)*x^8 + 1/1447775461176755326968167917924*(-777194053939504750117806035995392*mu^2 + 1890995121794801671145869539553344*mu - 876645782045536240390974061056645)*x^7 + 1/361943865294188831742041979481*(-414748214762691010862463616525824*mu^2 + 973121682645100372909396389646464*mu - 418896328835570100286899459532725)*x^6 + 1/723887730588377663484083958962*(-414748214762691010862463616525824*mu^2 + 973121682645100372909396389646464*mu - 418896328835570100286899459532725)*x^5 + 1/217751838276415937225703627775714195939081379*(672800666310179556189928998679850853080664787968*mu^2 - 1526117365640407582806158216579614341515061389568*mu + 564042671775972871996543624496911571404685888892)*x^4 + 1/217751838276415937225703627775714195939081379*(865029428113088000815622998302665382532283298816*mu^2 - 1962150898680524035036489135602361296233650358016*mu + 725197720854822263995556088638886306091739000004)*x^3 + 1/131003361624097910687645782812955154673509052734080825029361*(-786428455452167193729987728732383596614717985743145008976039936*mu^2 + 1769672774123062187998821137149428143343132562435288447526759424*mu - 635437204711676647634147301358815875716628444554384179695284828)*x;
X := HyperellipticCurve(f);


/* ------------------- STEP 0 ----------------------------*/
// Compute the Jacobian's period matrix
SetLogFile("Example2.out");
"The curve is the", X;


"Computing period matrix...";
g := Genus(X);
time PP := PeriodMatrix(X);


/* ------------------- STEP 1 ----------------------------*/
// Compute the CM algebra E
"Computing the CM field...";



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
        MonogenicGenerator := &+[ i * block[i] : i in [1..#block]];
        mu := P!MinimalPolynomial(MonogenicGenerator);
        EE := NumberField(mu);
        E, _ := OptimizedRepresentation(EE);
        //check, EtoEE := IsIsomorphic(E, EE);
        //assert check;

        iotaE1 := iota2(EE!E.1, MonogenicGenerator);

        iotaE1_big := ZeroMatrix(Q, Nrows(iotaE_gens[1]));
        InsertBlock(~iotaE1_big, iotaE1, block_starting_index, block_starting_index);
        iotaE1_big := BCM^-1*iotaE1_big*BCM;

        Append(~fields, <E, iotaE1_big, iotaE1>);
    end for;


// Define F as the compositum of the Galois closure of all E_i in E = E_1 x ... x E_t
E := fields[1,1];
F := NormalClosure(E);

// Save the Galois group of F/Q and fix an embedding F --> C
G, GAut, toAut := AutomorphismGroup(F);
emb_FC := hom< F -> CC | Roots(ChangeRing(DefiningPolynomial(F), CC))[1][1] >;	

// balh
conjugates := [r[1] : r in Roots(DefiningPolynomial(E), F)];
homEF := [* hom< E -> F | c > : c in conjugates *];
assert #homEF eq Degree(E);




"The CM field is the", E;
"The Galois closure of the CM field is the", F;
assert IsIsomorphic(E, NumberField(P!(x^8 - 4*x^7 + 26*x^6 - 64*x^5 + 152*x^4 - 202*x^3 + 240*x^2 - 149*x + 80)));



"------------------";
"STEP 1 OK!";
"------------------";
/* ------------------- STEP 2 ----------------------------*/
// Compute the CM type
"Computing the CM type...";


/* -- helper functions -- */
function AlgebraicMatrix(complex_matrix, closure_CMfield, emb_FC)
    /*  This function takes a matrix *M = complex_matrix* with algebraic coefficients
        in a field *F = closure_CMfield*, but stored as complex numbers.
        The output is the same matrix over F.   */
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
            px := MinimalPolynomialExtra(x, QQ);
            Append(~polys, <x, px, CC!x>); // store complex approx
        end if;
    end for;
    
    // Step 3: Match the entries
    images := [];
    for tup in polys do
        x_orig, px, x_cmplx := Explode(tup);
        roots := Roots(px, F);
        match := false;
        for rt in roots do
            x_K := F!rt[1]; // lift root to K
            if Abs(emb_FC(x_K) - x_cmplx) lt 10^-1000 then
                Append(~images, x_K);
                break;
            end if;
        end for;
    end for;
    assert #images eq #entries;


    // Reconstruct the matrix
    MK := Matrix(closure_CMfield, Nrows(M), Ncols(M), images);
    return MK;
end function;




/* -- CM type -- */
// Step 1: compute generators for End^0(J) as a Q algebra
    EndJ, cmplx_gens := EndomorphismRing(PP);
    Fgens := [ AlgebraicMatrix(M, F, emb_FC) : M in cmplx_gens ];
    Qgens := [ ChangeRing(A, Q) : A in Generators(EndJ) ];

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

// Step 5: recognize each simple component as a field Ei and appoint a generator iota(Ei.1)
    fields := [* *];
    block_starting_index := 1;
    for block in blocks do
        iotaE1_big := ZeroMatrix(Q, Nrows(Qgens[1]));
        InsertBlock(~iotaE1_big, iotaE1, block_starting_index, block_starting_index);
        iotaE1_big := BCM^-1*iotaE1_big*BCM;
        block_starting_index := block_starting_index + Nrows(block[1]);

        // Step 5.4: reconstruct complex monogenic generator for the E1 factor
        target := ChangeRing(PP, CC)*ChangeRing(iotaE1_big, CC);
        target := Submatrix(target, [1..Nrows(PP)], [1..Nrows(PP)]);
        Ma := target*Submatrix(ChangeRing(PP, CC), [1..Nrows(PP)], [1..Nrows(PP)])^-1;
        Ma := AlgebraicMatrix(Ma, F, emb_FC);

        Append(~fields, <E, iotaE1_big, Ma>);
    end for;

iotaE := fields;

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
diagonalized_complex, BCM_cmplx := Diagonalisation([Ma]);
block_starting_index := 1;
D := BCM_cmplx * Ma * BCM_cmplx^-1;
CM_type := [* hom< E -> F | D[i,i] > : i in [1..Nrows(D)] | D[i,i] ne 0 *];
Append(~CM_types, CM_type);
CM_types;

count := 0;
for g in G do
    if g^2 eq Identity(G) and &and[g*h*g^-1*h^-1 eq Identity(G): h in G] and (not (g eq Identity(G))) then
        complex_conjugation_onF := g;
        count +:= 1;
    end if;
end for;
assert count eq 1;

c := toAut(complex_conjugation_onF);

homEF := CM_type cat [* gg : gg in homEF, ff in CM_type | gg(E.1) eq c(ff(E.1)) *];







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
function ReflexField(CM_type)
    /* Given a field E (subfield of F) and its CM-type
        computes the reflex field E* */
    

    // Compute CM lift
    CM_lift := [];
    for g in G do
        if &or[toAut(g)(E.1) eq sigma(E.1) : sigma in CM_type] then
            Append(~CM_lift, g);
        end if;
    end for;

    // Subgroup of G that fixes the inverse orbit
    Hstar_gen := [ g : g in G | &and[ h * g  in CM_lift: h in CM_lift ] ];
        // ATCHUNG!! hg vs gh
    Hstar := sub< G | Hstar_gen >;

    // Reflex field = fixed field of H
    Estar := FixedField(F, [toAut(h) : h in Hstar]);

    return Estar;
end function;

"Computing reflex field...";
reflex_fields := [* *];
Estar := ReflexField(CM_type);
Append(~reflex_fields, Estar);

"The reflex field is the", Estar; 

// balh
conjugates := [r[1] : r in Roots(DefiningPolynomial(Estar), F)];
homEstarF := [* hom< Estar -> F | c > : c in conjugates *];
assert #homEstarF eq Degree(Estar);



/* -- reflex norm matrix -- */
function ReflexNormMatrix(CM_type)
    /* Given a field E (subfield of F) and its CM-type
        computes the reflex norma matrix Z[Hom(E*,F)]-> Z[Hom(E,F)] */
    
    // Get all embeddings
    sigmas := homEF;
    etas := homEstarF;

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

    return M;
end function;

"Computing reflex norm matrix...";
// Diagonal join of reflex norm matrices of blocks
reflex_matrix := [* *];
for i in [1..1] do
    CM_type := CM_types[i];
    ReflexNorm := ReflexNormMatrix(CM_type);
    Append(~reflex_matrix, ReflexNorm);
end for;
reflex_matrix := BlockDiagonalMatrix(reflex_matrix);



/* -- norm matrix -- */
function EmbeddingToAutomorphismMatrix()
    /* Given a field E (subfield of F)
        computes the norm matrix Z[Hom(F,F)]-> Z[Hom(E,F)] */

    // Step 1: Get all embeddings E -> F
    sigmas := homEstarF;
    etas := [ toAut(g) : g in G ];
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

    return M;
end function;

"Computing norm matrix...";
norm_matrix := [* *];
// Horizontal join of norm matrices of extensions F/E_i*
NormMatrix := EmbeddingToAutomorphismMatrix();
Append(~norm_matrix, NormMatrix);
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




/* -- ad hoc computation -- */
//E := iotaE[1,1];
CM_type := CM_types[1];

/* Let E = Q(alpha). We compute the tangent representation
    of alpha on the Tait basis:
    x^i-1 dx/y for i = 1...g and [y/x^i] for i = 1...g.
    
    The action on the holomorphic ones is given by M_alpha = iotaE[1,3],
    while the action on the quotient H1(X, O_X) = H1_dR(X/k) / H0(X, Omega1)
    is given by M_\bar{alpha} by the Rosati-involution trick.

    We compute \bar{alpha} in E and the matrix M_\bar{alpha} using the iota2-tric:
    write \bar{alpha} as a linear combination of powers of alpha
    and then M_\bar{alpha} as the same linear combinations of M_alpha.  */
conjugates_of_E1 := Roots(MinimalPolynomial(E.1), E);
assert #conjugates_of_E1 eq 2;
conjugate_of_E1 := [ rr[1] : rr in conjugates_of_E1 | not rr[1] eq E.1 ][1];
M_alphabar := iota2(conjugate_of_E1, Ma);
N := Transpose(M_alphabar);

/* We compute an eigenbasis for the E-action.
    Notice there is no need to compute the Tait basis [y/x^i] explicitly
    to diagonalize the block N of the tangent representation matrix.
    
    Once the matrix is diagonal, we reorder the basis so that
    omega_i and omega_i+g correspond to a conjugate pair of embeddings. */
diagonalized_complex2, BCM_cmplx2 := Diagonalisation([N]);
N_diag := diagonalized_complex2[1];
assert N_diag eq BCM_cmplx2 * N * BCM_cmplx2^-1;
assert IsDiagonal(N_diag);
perm := [ i : i in [1..#CM_type], j in [1..#CM_type] | toAut(complex_conjugation_onF)(CM_type[j](E.1)) eq N_diag[i,i] ];
perm_matrix := PermutationMatrix(F, perm);
N_diag := perm_matrix * N_diag * perm_matrix^-1;
perm := [ i : i in [1..#CM_type], j in [1..#CM_type] | toAut(complex_conjugation_onF)(CM_type[j](E.1)) eq N_diag[i,i] ];
BCM_cmplx2 := perm_matrix * BCM_cmplx2;
assert N_diag eq BCM_cmplx2*N*BCM_cmplx2^-1;

/* We rescale the differential forms of the second kind in order
    to guarantee that < omega_i, omega_c(i) >_dR = 1.
    
    We then compute the constant alpha_f in chi_dR.
    We need a non-trvial coefficient on each...
    line (?) of the base change matrix. */
AA := Transpose(BCM_cmplx);
BB := Transpose(BCM_cmplx2); // WHY is this t here?
// Check this rescaling is the correct way around: we need to take the scalar product of COLUMNS, right?
rescaling_factors := [ &+[ AA[i, j]*BB[i, j] : i in [1..Nrows(AA)]] : j in [1..Ncols(AA)] ];
rescaling_factors := [ x^-1 : x in rescaling_factors];
BB := BB * DiagonalMatrix(F, rescaling_factors);

function NonZeroRepresentative(MM)
    /* Takes a matrix MM as input,
        and outputs a non-zero entry for every COLUMN. */ 
    all_representatives := [ [ MM[i, j] : i in [1..Ncols(MM)] | not MM[i,j] eq 0 ] : j in [1..Nrows(MM)] ];
    for i in [1..#all_representatives] do
        assert #all_representatives[i] gt 0;
    end for;
    return [ rep[1]^-1 : rep in all_representatives ]; //alpha = 1/a
end function;

alpha := NonZeroRepresentative(AA) cat NonZeroRepresentative(BB);





/* --------------------- */
//xi := E.1-1/2;

/* We compute the Bertrand artimetic constant constant B, such that
    int_lambda omega_i * int_lambda omega_c(i) = B * (2 pi i).
    
    We do this by computing the E-action on Betti homology,
    lucky us we knoe the action as a 2gx2g integral matrix
    in MAGMA's homology basis (which we do not wish to know).
    Let A be the matrix corresponding to a such that E = Q(a),
    we have already computed A := iotaE[1,2];
    
    We then reconstruct the matrix in the span of 1, A, ..., A^7
    sending lambda_1 to lambda_m; say M.
    We then recognize the element of E corresponding to M,
    by using the same coefficients, using a (:= E.1) insted of M. */

A := iotaE1_big;
I := IdentityMatrix(BaseRing(A), 8);
V := VectorSpace(Q, 8);
u := Basis(V)[1];
cols := [u];
for k in [1..7] do
    Append(~cols, Transpose(A^k)[1]);
end for;
M := Transpose(Matrix(cols));   // columns are u, Au, ..., A^7 u


ee_coeff := [ Transpose(M^-1)[m] : m in [1..8] ];
ee := [  ];
for coeff in ee_coeff do
    Append(~ee, E!coeff[1] + &+[ E.1^k * E!coeff[k+1] : k in [1..7] ]);
end for;






/* --------------------- */

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

function MTequation_to_IndexTuple(f)
    tuple := [];
    for i in [1..4] do
        if f[i] ge 0 then
            tuple := tuple cat [ i : j in [1..f[i]]];
        else 
            tuple := tuple cat [ i+g : j in [1..-f[i]]];
        end if;
    end for;
    
    for i in [5..8] do
        if f[i] ge 0 then
            tuple := tuple cat [ i : j in [1..f[i]]];
        else 
            tuple := tuple cat [ i-g : j in [1..-f[i]]];
        end if;
    end for;

    return tuple;
end function;


function GaloisActionOnIndex(tau, index)
    for j in [1..8] do 
        if homEF[j](E.1) eq toAut(tau)(homEF[index](E.1)) then
            return j;
        end if;
    end for;
end function;


/* -- compute periods -- */
function ComputePeriod(PP, If)
    // Pick an arbitrary cycle sigma:
    cycle_index := 1;
    n := Integers()!(#If/2);

    // Basis-change of the big period matrix:
    PP := ChangeRing(PP, CC);
    elementary_period := (ApplyEmbeddingToMatrix(BCM_cmplx, emb_FC)*PP);

    period := CC!1;
    for sigma_index in If do
        if sigma_index le 4 then
            new_factor := elementary_period[sigma_index, cycle_index];
        else 
            new_factor := (2*Pi(CC)*CC.1)/(elementary_period[sigma_index-g,cycle_index]);
        end if;

        period := period * new_factor;
    end for;
    period := period / (2*Pi(CC)*CC.1)^n;

    return MinimalPolynomialExtra(period, NumberFieldExtra(DefiningPolynomial(KK))), period;
end function;

function ComputeArithmeticFactor(If)
    n := Integers()!(#If/2);
    arithmetic_factor := F!1;
    for sigma_index in If do
        if sigma_index gt 4 then
            sigma := homEF[sigma_index-g];
            c := toAut(complex_conjugation_onF);
            arithmetic_factor := arithmetic_factor / &+[ c(sigma(ee[m+g]))*sigma(ee[m]) - c(sigma(ee[m]))*sigma(ee[m+g]) : m in [1..g]];
        end if;
    end for;
    return arithmetic_factor;
end function;


function ComputeCorrectPeriod(PP, If)
    polyperiod, period := ComputePeriod(PP, If);
    arithmetic_factor := ComputeArithmeticFactor(If);

    _, _ := IsSubfield(BaseRing(Parent(polyperiod)), F);
    count := 0;
    for rr in Roots(polyperiod, F) do
        if Norm(emb_FC(rr[1]) - period) lt 10^-1000 then
            true_period := rr[1];
            count := count +1;
        end if; 
    end for;
    
    return true_period * arithmetic_factor;
end function;


function chi_dR(tau, If)
    chi := F!1;
    for i in If do
        tau_i := GaloisActionOnIndex(tau, i);
        chi := chi * toAut(tau)(alpha[i]) / alpha[tau_i];
    end for;
    return chi;
end function;


subgroups := [* *];
fields := [* *];
for f in MTequations do
    "Computing period cocylce relation for the equation", f;
    If := MTequation_to_IndexTuple(f);
    period_f := ComputeCorrectPeriod(PP, If);

    Hf := [];
    for tau in G do
        tauIf := [ GaloisActionOnIndex(tau, i) : i in If ];
        period_tauf := ComputeCorrectPeriod(PP, tauIf);
        if chi_dR(tau, If) * toAut(tau)(period_f) eq period_tauf then
            Append(~Hf, tau);
        end if;
    end for;

    &and[ toAut(g)(Estar.1) eq Estar.1 : g in Hf ];
    Hf := sub< G | Hf >;
    Kf := FixedField(F, Hf);
    "The corresponding Tate class is defined over the", Kf;
    assert IsSubfield(Kf, Estar);
end for;















"Small checks...";
//Eguess := NumberField(x^8 - 4*x^7 + 26*x^6 - 64*x^5 + 152*x^4 - 202*x^3 + 240*x^2 - 149*x + 80);
"The compositum k.E* is contained in F:", IsSubfield(KK, F);
"The field k is contained in E*:", IsSubfield(KK, Estar);

"Checking irreducibility of CM type...";
cmt := CM_types[1];
CMtype_extendF := [ ];
for g in G do
    for sigma in cmt do
        if (toAut)(g)(E.1) eq sigma(E.1) then
            Append(~CMtype_extendF, toAut(g));
        end if;
    end for; 
end for;
gggg := [];
for g in G do
    g_cmt := [ toAut(g)*ff : ff in CMtype_extendF ];
    if Set(CMtype_extendF) eq Set(g_cmt) then
        Append(~gggg, g);
    end if;
end for;

"------------------";

