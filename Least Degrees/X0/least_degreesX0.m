// The aim of this code is to compute the least degree over Q 
// of a CM point on the modular curve X_0(N), which we denote d_{CM}(X_0(N)). 

// We then use this to try to guarantee the existence of a sporadic CM point on X_0(N), or else
// to try to prove there can be no such point on this curve. 



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Computing d_{CM,O}(X_1(N)) for a given order O
// Note: this is the same code as in least_degreesX1.m file
// and is only used in this file when we compute *all* of the 
// minimizing orders for a given N
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////


// T_Tilde_PrimePower : given conductor f = [\mathcal{O_K} : \mathcal{O}] of an order \mathcal{O} in an 
// imaginary quadratic field K, d_K the discriminant of K, l a rational prime, and a and b non-negative 
// integers, computes \tilde{T}(\mathcal{O},l^a, l^b) as in Thm 4.1 of BC19

T_Tilde_PrimePower := function(f,d_K,l,a,b)

    d := f^2*d_K;

    if l^b eq 2 then
        if a eq 0 then 
            if KroneckerSymbol(d, 2) ne -1 then
                return 1;
            else
                return 3;
            end if;
        else
            return 2 - KroneckerSymbol(d, 2);
        end if;
    elif (l^b ge 3) then
        c := Valuation(f,l);
        if (KroneckerSymbol(d,l) eq -1) then
            return l^(2*b-2)*(l^2-1);
        elif (KroneckerSymbol(d,l) eq 1) then
            if a eq 0 then
                return l^(b-1)*(l-1);
            else
                return l^(a+b-2)*(l-1)^2;
            end if;
        elif (f mod l eq 0) and (KroneckerSymbol(d_K,l) eq 1) then
            return l^(a+b-1)*(l-1);
        elif (KroneckerSymbol(d_K,l) eq 0) then
            if b le 2*c+1 then
                return l^(a+b-1)*(l-1);
            else
                return l^(Maximum({a+b-1,2*b-2*c-2}))*(l-1);
            end if;
        elif (f mod l eq 0) and (KroneckerSymbol(d_K,l) eq -1) then
            if b le 2*c then
                return l^(a+b-1)*(l-1);
            else
                return l^(Maximum({b-1,2*b-2*c-1}))*(l-1);
            end if;
        end if;
    end if; 
end function; 



// T : given conductor f = [\mathcal{O_K} : \mathcal{O}] of an order \mathcal{O} in an 
// imaginary quadratic field K, d_K the discriminant of K, and N>1 a positive integer,
// computes T\mathcal{O},N) as in Thm 4.1 of BC19

T := function(f,d_K,M,N) //ONLY use N>1

    if d_K lt -4 then
        w_K := 2;
    elif d_K eq -4 then
        w_K := 4;
    elif d_K eq -3 then
        w_K := 6;
    end if;
    
    w := 2;
    if f eq 1 then
        w := w_K;
    end if;

    d := f^2*d_K;

    if (N eq 2) and (M eq 1) then
        if (d ne -3) and KroneckerSymbol(2,d) eq -1 then
            return 3;
        else
            return 1;
        end if;

    elif (N eq 2) and (M eq 2) then
        return ( 2*(2-KroneckerSymbol(d,2)) ) / w;

    elif (N eq 3) and (M eq 1) then
        if KroneckerSymbol(d,3) eq -1 then
            return 8/w;
        else
            return 1;
        end if;

    elif (N eq 3) and (M eq 3) then
        return ( 2*(3-KroneckerSymbol(d,3)) )/w;

    elif (N ge 4) then
        //FM := Factorization(M);
        FN := Factorization(N);
        P := 1;
        for pair in FN do //f, d_K, l, a, b
            P := P*T_Tilde_PrimePower(f,d_K,pair[1],Valuation(M, pair[1]), pair[2]);
        end for;
        return P/w; 

    end if;
end function;



// T0_PrimePower_need2 : given conductor f = [\mathcal{O_K} : \mathcal{O}] of an order \mathcal{O} in an 
// imaginary quadratic field K, d_K the discriminant of K, l a rational prime, and b a non-negative integer,
// returns true if T^\circ(\mathcal{O},l^b) = 2*T(\mathcal{O},l^b), returns
// false if T^\circ(\mathcal{O},l^b) = T(\mathcal{O},l^b)

T0_PrimePower_need2 := function(f,d_K,l,b)

    d := f^2*d_K;
    
    // Inert Case
    if KroneckerSymbol(d,l) eq -1 then
        return false;
    
    // Split Case
    elif KroneckerSymbol(d,l) eq 1 then
        if l^b ge 3 then
            return true;
        elif l^b eq 2 then
            return false;
        end if;
        
    // Ramified Case
    else
        c := Valuation(f,l);
        if KroneckerSymbol(d_K, l) eq 0 then
            if l eq 2 then
                if c eq 0 then
                    return false;
                else
                    if Valuation(d_K,2) eq 2 then
                        if b le 2*c then   
                            return false;
                        else
                            return true;
                        end if;
                    elif Valuation(d_K,2) eq 3 then
                        return false;
                    end if;
                end if;
            else
                return false;
            end if;
        elif f mod l eq 0 then
            if KroneckerSymbol(d_K,l) eq 1 then
                if l eq 2 then
                    if c eq 1 then
                        if b eq 1 then
                            return false;
                        else
                            return true;
                        end if;
                    elif c ge 2 then
                        if b le 2*c-2 then
                            return false;
                        else 
                            return true;
                        end if;
                    end if;
                else
                    if b le 2*c then
                        return false;
                    else
                        return true;
                    end if;
                end if;
            
            elif KroneckerSymbol(d_K,l) eq -1 then
                if l eq 2 then
                    if c eq 1 then
                        if b eq 1 then
                            return false;
                        else
                            return true;
                        end if;
                    elif c ge 2 then
                        if b le 2*c-2 then
                            return false;
                        else 
                            return true;
                        end if;
                    end if;
                else
                    return false;
                end if;
            end if;
        end if;
    end if;
end function; 



// T0 : given conductor f = [\mathcal{O_K} : \mathcal{O}] of an order \mathcal{O} in an imaginary
// quadratic field K, d_K the discriminant of K, and N a positive integer, computes T^\circ(\mathcal{O},N) 
// -- the least degree over Q(f) in which there is an \mathcal{O}-CM elliptic curve with a rational
// point of order N

T0 := function(f,d_K,M,N) // generalized to include M>1 in least_degreesXMN.m
    FN := Factorization(N);
    need2 := false;
    
    for pair in FN do
        if T0_PrimePower_need2(f,d_K,pair[1],pair[2]) eq true then
            need2 := true;
            break;
        end if;
    end for;
    
    if need2 eq true then
        return 2*T(f,d_K,1,N);
    elif need2 eq false then
        return T(f,d_K,1,N); 
    end if;
end function;



// load list of quadratic number fields of discriminant -3 to -40,000 obtained from LMFDB

R<x> := PolynomialRing(RealField(),1);
load "fields.m";



// clean up list to get list of just [disc, classnum]

disc_ClassNumber_list := [];

for list in data do
    h := 1;
    for k in [1..#list[4]] do
        h := h * list[4][k];
    end for;
    Append(~disc_ClassNumber_list,[list[2], h]);
end for;



// d_OCM_X1 : given conductor f = [\mathcal{O_K} : \mathcal{O}] of an order \mathcal{O} in an imaginary
// quadratic field K d_K the discriminant of K, and N a positive integer, computes 
// d_{\mathcal{O},CM}(X_1(N)) = T^\circ(\mathcal{O},N)*[Q(f):Q] -- the least degree over Q in which 
// there is an \mathcal{O}-CM elliptic curve with a rational point of order N.

// NOTE: This function is not used below, as the list of orders we loop over is already sorted by 
// class number, and the factor [Q(f) : Q] here is equal to the class number of O. 

d_OCM_X1 := function(f,d_K,N)
    
    if d_K lt -4 then
        w_K := 2;
    elif d_K eq -4 then
        w_K := 4;
    elif d_K eq -3 then
        w_K := 6;
    end if;
    
    found_disc := false;
    for j in [1..#disc_ClassNumber_list] do
        if d_K eq disc_ClassNumber_list[j][1] then
            h_K := disc_ClassNumber_list[j][2];
            found_disc := true;
            break;
        end if;
    end for;

    if found_disc eq false then
        return "discriminant -D not in list";
    else
        if f eq 1 then
            return T0(f,d_K,1,N)*h_K;
        else
            Prod := 1;
            for pair in Factorization(f) do
                Prod := Prod*(1-KroneckerSymbol(d_K,pair[1])*(1/pair[1]));
            end for;
            return (T0(f,d_K,1,N)*(2/w_K)*f*Prod*h_K);
        end if;
    end if;
end function; 



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Computing d_{CM}(X_0(N))
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////



// loading sequence
// dcm_list_X1 : List of the least degree of a CM point on X_1(N) for each 1 \leq N \leq 1,000,000.
// For each N, includes an order O which gives the least degree.
// Data is [N, d_CM(X_1(N)), f(O), Disc(O_K))], 
// where f(O):=[O_K:O] is the conductor of O and Disc(O_K) is the fundamental discriminant of K.

load 'dcm_list_X1_1mil.m'; 



// is_of_Type1 : given natural N, returns true if N is of Type 1 and false otherwise. N is Type 1
// if N>=4, 9 does not divide N, and no prime which is 2 (mod 3) divides N. This is equivalent to
// d_{CM}(X_1(N)) being phi(N)/3, with a minimizing order O_K where K = Q(sqrt(-3))

is_of_Type1 := function(N)
    if N lt 4 then
        return false;
    elif N mod 9 eq 0 then
        return false;
    end if;
    FN := Factorization(N);
    Heegner := true;
    for pair in FN do
        if pair[1] ne 3 then
            if KroneckerSymbol(-3, pair[1]) ne 1 then
                Heegner := false;
            end if;
        end if;
    end for;
    if Heegner eq true then
        return true;
    else
        return false;
    end if;
end function;



// is_of_Type2 : given natural N, returns true if N is of Type 2 and false otherwise. N is Type 2
// if N>=7, 4 does not divide N, and no prime which is 3 (mod 4) divides N. This guarantees that 
// d_{CM}(X_1(N)) = phi(N)/2, with a minimizing order O_K where K = Q(i), as long as N is not Type 1. 

is_of_Type2 := function(N)
    if N lt 5 then
        return false;
    elif N mod 4 eq 0 then
        return false;
    end if;
    FN := Factorization(N);
    Heegner := true;
    for pair in FN do
        if pair[1] ne 2 then
            if KroneckerSymbol(-4, pair[1]) ne 1 then
                Heegner := false;
            end if;
        end if;
    end for;
    if Heegner eq true then
        return true;
    else
        return false;
    end if;
end function;



// declaring sequence
// dcmX0eq1_list : list of all N for which d_{CM}(X_0(N)) = 1

dcmX0eq1_list := [1,2,3,4,6,7,9,11,14,19,27,43,67,163]; 



// dcm_X0 : given natural number N>1, computes d_{CM}(X_0(N)) utilizing pre-computed
// d_{CM}(X_1(N)) value (in dcm_list_X1). Returns sequence of lists
// [* N, d_{CM}(X_0(N)), f(O), Disc(O_K) *] for a single minimizing order O of conductor f, 
// fundamental discriminant d_K, and class number h(O). 

// NOTE: Takes into account Type1, Typ2, and N in dcmX0eq1_list to increase speed

// NOTE: Exactness of calculation for N not of type 1 or type 2 depends on exactness in
// called dcm_list_X1


dcm_X0 := function(N)

	if N in dcmX0eq1_list then
		return [* N,1,dcm_list_X1[N][3],dcm_list_X1[N][4] *];

	elif not (is_of_Type1(N) or is_of_Type2(N)) then 
        return [* N, (2 * dcm_list_X1[N][2] / EulerPhi(N)), dcm_list_X1[N][3], dcm_list_X1[N][4] *];

    elif is_of_Type1(N) then
        return [* N, 2, 1, -3 *];

    elif is_of_Type2(N) then
        return [* N, 2, 1, -4 *];

    end if;
end function; 




// loading sequence
// dcm_list_X0 : List of the least degree of a CM point on X_0(N) for each 1 \leq N \leq 1,000,000.
// For each N, includes an order O which gives the least degree.
// Data is [N, d_CM(X_0(N)), f(O), Disc(O_K))], 
// where f(O):=[O_K:O] is the conductor of O and Disc(O_K) is the fundamental discriminant of K.

load "dcm_list_X0_1mil.m";

// loading sequence
// dcm_list_X1_all_min_orders : List containing least degree of a sporadic CM point on X_1(N) and
// all imaginary quadratic orders O for which there is an O-CM elliptic curve 
// giving this degree for each 1 \leq N \leq 10,000.

// ith element in list is list [* N,dcm,count,orders *], where dcm is the least degree d_{CM}(X_1(N)),
// count is the number of minimizing orders, that is orders O such that d_{O,CM}(X_1(N)) = d_{CM}(X_1(N)),
// and orders is the list of these minimizing orders. Element of orders corresponding to O given as 
// [f,d_K,h(O)] = [conductor, fundamental discriminant, class number]. 

load "dcm_list_all_min_orders_X1_10k.m";

// load list of all (not just maximal) orders of class number up to 100. The ith element 
// is the complete list of pairs [f,d_K] = [conductor, fundamental discrimint] for imaginary quadratic
// orders of class number i. Generated using list of maximal orders by M. Watkins. 

load 'cond_disc_list_allO.m';



// dcm_X0_all_minimizing_orders : given natural number N > 1, minimizes d_{CM,O}(X_0(N)) over imaginary
// quadratic orders O of class number up to 100 using previously computed value and list of minimizing
// orders (in dcm_list_X0 and dcm_list_X1_all_min_orders). Returns list [dcm, orders],
// where dcm is this minimum d_{CM,O}(X_0(N)) over such orders O and orders is complete sequence of sequences 
// [f, d_K, h(O)] for all minimizing orders O of class number up to 100, where f is the conductor, 
// d_K the fundamental discriminant, and h(O) is the class number of O

// NOTE: Exactness of calculation for N not of type 1 or type 2 depends on exactness in
// called dcm_list_X1_all_min_orders


dcm_X0_all_minimizing_orders := function(N)

    // outputs for N<=3 based on rational isogenies and Theorem 3.7 parts (a) and (d) (i)

    if N le 3 then
        if N eq 1 then
            return [*1,[[ 1, -3, 1 ], [ 2, -3, 1 ], [ 3, -3, 1 ], [ 1, -4, 1 ], 
                [ 2, -4, 1 ], [ 1, -7, 1 ], [ 2, -7, 1 ], [ 1, -8, 1 ], [ 1, -11, 1 ],
                [ 1, -19, 1 ], [ 1, -43, 1 ], [ 1, -67, 1 ], [ 1, -163, 1 ]]*];

        elif N eq 2 then
            return [*1,[[ 1, -3, 1 ], [ 2, -3, 1 ], [ 3, -3, 1 ], [ 1, -4, 1 ],
                [ 2, -4, 1 ], [ 1, -7, 1 ], [ 2, -7, 1 ], [ 1, -8, 1 ], [ 1, -11, 1 ],
                [ 1, -19, 1 ], [ 1, -43, 1 ], [ 1, -67, 1 ], [ 1, -163, 1 ]]*];

        elif N eq 3 then
            return [*1,[[ 1, -3, 1 ], [ 2, -3, 1 ], [ 3, -3, 1 ]]*];

        end if;

    else 
        dcm := dcm_list_X0[N][2];

        if dcm eq 1 then 

            PhiN := EulerPhi(N);
            orders := []; // initializing list for minimizing orders
            
            for order in cond_disc_list_allO[1] do 
                if order eq [1,-3] and is_of_Type1(N) then // d_{-3,CM}(X_0(N)) = 2

                elif order eq [1,-4] and is_of_Type2(N) then // d_{-4,CM}(X_0(N)) = 2

                elif dcm eq (2 * d_OCM_X1(order[1],order[2],N) / PhiN) then
                    Append(~orders, [order[1],order[2],1]);

                end if;

            end for;

        elif dcm eq 2 then

            PhiN := EulerPhi(N);
            orders := []; // initializing list for minimizing orders

            // Note: going over the orders [1,-3] and [1,-4] again will not double count, as in the type 1 case
            // we have d_{-3,CM}(X_0(N)) = d_{-3,CM}(X_1(N))/(Phi(N)/6), which is strictly larger than 2,
            // and similarly in the type 2 case with 6 replaced by 4. 
            for order in cond_disc_list_allO[1] do 
                if order eq [1,-3] and is_of_Type1(N) then
                    Append(~orders, [1,-3,1]);

                elif order eq [1,-4] and is_of_Type2(N) then
                    Append(~orders, [1,-4,1]);

                elif dcm eq (2 * d_OCM_X1(order[1],order[2],N) / PhiN) then
                    Append(~orders, [order[1],order[2],1]);
                end if;

            end for;

            for order in cond_disc_list_allO[2] do
                if dcm eq (2 * d_OCM_X1(order[1],order[2],N) / PhiN) then
                    Append(~orders, [order[1],order[2],2]);
                end if;
            end for;

        else 
            // outside of above cases, we know d_{O,CM}(X_0(N)) = d_{O,CM}(X_1(N)/(phi(N)/2),
            // so the minimizing order list is the same as in the X_1(N) case
            orders := dcm_list_all_min_orders_X1[N][4];

        end if; 

        return [* dcm, orders *];
    end if;    
end function;



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Return to Guaranteeing a Sporadic CM Point on X_0(N)
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////



// psi_from_fact: Given natural N, factorization of N (sequence of pairs (p,a)), computes psi(N)

psi_from_fact := function(N,F)
    M := 1;
        for i in [1..#F] do
            M := M * (F[i][1]+1)*F[i][1]^(F[i][2]-1);
        end for;
    return M;
end function;


// loading sequence
// further_bads_X0_X1 = sequence of N for which we have not guaranteed a sporadic CM point on X_1(N) 
// using Frey-Faltings with upper bound on d_{CM}(X_1(N)) from Thm 5.1 (using any imaginary quadratic 
// discriminant D satisfying the Heegner hypothesis) and lower bound on 
// \frac{\gamma}{2} from JKS04

    // load 'further_bads_X0_X1.m'; 



// generating sequence
// hyper_bads_X0 : N in further_bads_X0_X1 such that X_0(N) is still not determined to have a sporadic CM point
// by computing d_{CM}(X_0(N)) exactly and comparing to lower bound on the gonality of X_0(N). 

    // hyper_bads_X0 := [N : N in further_bads_X0_X1 | dcm_X0(N)[2] gt ((119 * psi_from_fact(N, Factorization( N ))) / 24000)];

    // SetOutputFile("hyper_bads_X0.m");
    // print hyper_bads_X0;
    // UnsetOutputFile();


// NOTE: Size of further_bads_X0_X1 lowered by 295 to 359 to get hyper_bads_X0, 
// with largest N in hyper_bads_X0 being 720



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Guaranteeing NO Sporadic CM Point on X_0(N) for bad N
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////



// Notation: delta(X) is the least degree d for which 
// X has infinitely many closed points of degree d.

// declaring sequence
// delta_1_X0 : sequence of all N for which delta(X_0(N)) = 1
// for all of these N, X_0(N) has no sporadic CM point

delta_1_X0 := [1,2,3,4,5,6,7,8,9,10,12,13,16,18,25];


// declaring sequence
// delta_2_X0 : sequence of all N for which delta(X_0(N)) = 2
// for all of these N, X_0(N) has a sporadic CM point iff d_{CM}(X_0(N)) = 1

delta_2_X0 := [11,14,15,17,19,20,21,22,23,24,26,27,28,29,30,31,32,33,35,36,37,39,40,41,43,46,47,
48, 49, 50, 53, 59, 61, 65, 71, 79, 83, 89, 101, 131]; 


// Here we create list no_sporadic_CM_X0 of values of N for which
// we determine there is no sporadic CM point using that delta(X_0(N)) <= 2. 

// generating sequence 
// no_sporadic_CM_X0 = sequence of all N such that, using exact d_{CM}(X_0(N)) 
// calculations from dcm_X0 function, we can provably say X_0(N) has no sporadic CM point
// via fact that delta(X_0(N)) <= 2

    // load "hyper_bads_X0.m";

    // no_sporadic_CM_X0 := delta_1_X0;

    // for N in delta_2_X0 do
    //     if dcm_X0(N)[2] ne 1 then
    //         Append(~no_sporadic_CM_X0, N);
    //     end if;
    // end for;

    // Sort(~no_sporadic_CM_X0);

    // SetOutputFile("no_sporadic_CM_X0.m");
    // print no_sporadic_CM_X0;
    // UnsetOutputFile();

