// The aim of this code is to compute the least degree over Q 
// of a CM point on the modular curve X_0(N), which we denote d_{CM}(X_0(N)). 

// We then use this to try to guarantee the existence of a sporadic CM point on X_0(N), or else
// to try to prove there can be no such point on this curve. 


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

