// The aim of this code is to compute, for an integer N >= 2, the least degree over Q 
// of a CM point on the modular curve X_1(N), which we denote d_{CM}(X_1(N)). 

// We then use this to try to guarantee the existence of a sporadic CM point on X_1(N), or else
// to try to prove there can be no such point on this curve. 


//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Computing d_{CM,O}(X_1(N)) for a given order O
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
// Minimizing d_{O,CM}(X_1(N)) over orders O of class
// number <= 100
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



// sequence of all imaginary quadratic orders with class number one, by [f, D_K]

classNum1_orders:=[[1,-3],[1,-4], [1,-7], [1,-8], [1,-11], [2, -3], [2,-4], [1,-19], [3,-3], [2, -7], [1,-43], [1,-67], [1,-163]];



// loading sequence
// classnum_disc_list = sequence of (abs values of) discriminants of imaginary quadratic fields of class number 
// up to 100. The ith element is the complete sequence of (abs values of) discriminants of such fields
// with class number i. Modified from list of M. Watkins.

// only need if using the dcm_over_orders function, not for dcm_over_nonmax_orders

    // load 'classnum_disc_list.m';



// dcm_over_orders : given natural number N>1, determines the minimum value h_0 of d_{CM,O}(X_1(N)) 
// over im quad orders O of class number 1. Then, minimizes d_{CM,O}(X_1(N)) over such orders
// and maximal im quad orders of class numbers 2 to h_0. Returns list 
// [conductor of O, discriminant of O, h(O), d_{CM,O}(X_1(N))] for such order O minimizing d_{CM,O}.

// NOTE: will let you know if h_0 is above 100

// NOTE: dcm_over_orders only gives an upper bound on d_{CM}(X_1(N)) (unless it gives 1), as 
// the second part only computes over class numbers of maximal orders; we'd need to compute class 
// numbers up to h_0 for all orders to get an exact value. This is done with the
// dcm_over_nonmax_orders function below, which replaces this one. 

    // dcm_over_orders := function(N)
    // 	CondDiscT0h:= [classNum1_orders[1][1], classNum1_orders[1][2],T0(classNum1_orders[1][1], classNum1_orders[1][2], 1, N),1];
    // 	for i in [1..#classNum1_orders] do
    // 		if CondDiscT0h[3] gt T0(classNum1_orders[i][1], classNum1_orders[i][2], 1, N) then
    // 			CondDiscT0h:= [classNum1_orders[i][1],classNum1_orders[i][2],T0(classNum1_orders[i][1], classNum1_orders[i][2], 1, N),1];
    //         end if;
    // 	end for;
    // 	if CondDiscT0h[3] eq 1 then
    // 		return [CondDiscT0h[1], CondDiscT0h[2], CondDiscT0h[4], CondDiscT0h[3]];
    //     else
    // 		h0 := CondDiscT0h[3]; // upper bound for h_{minimizing Disc}
    // 		h := 2;
    // 		while h le h0 and h le 100 do
    // 			for D in classnum_disc_list[h] do
    // 				if T0(1, -D, 1, N) * h lt CondDiscT0h[3] * CondDiscT0h[4] then
    // 				    CondDiscT0h := [1, -D, T0(1, -D, 1, N), h];
    // 				end if;
    // 			end for;
    // 			h:=h+1;
    // 		end while;
    // 	end if;
    //     if CondDiscT0h[3] gt 100 then
    //         print "Note: h0 > 100";
    //     end if;
    // 	return [CondDiscT0h[2], CondDiscT0h[1], CondDiscT0h[4], CondDiscT0h[4]*CondDiscT0h[3]];
    // end function;



// load list of all (not just maximal) orders of class number up to 100. The ith element 
// is the complete list of pairs [f,d_K] = [conductor, fundamental discrimint] for imaginary quadratic
// orders of class number i. Generated using list of maximal orders by M. Watkins. 

load 'cond_disc_list_allO.m';


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


// declaring sequences
// exceptional_N : list of all N not of type 2 for which d_{CM}(X_1(N)) = phi(N)/2
// exceptions_to_type_2 : list of [f,d_K,N] for N in exceptional_N, where f, d_K are conductor, fundamental
// discriminant of an order O such that d_{O,CM}(X_1(N)) = d_{CM}(X_1(N)) = phi(N)/2

exceptional_N := [9,11,14,27]; 
exceptions_to_type_2 := [[1,-3,9],[3,-3,9],[1,-11,11],[1,-7,14],[2,-7,14],[3,-3,27]];



// dcm_over_nonmax_orders : given natural number N>1, minimizes d_{CM,O}(X_1(N)) over imaginary
// quadratic orders O of class number up to 100. Returns sequence
// [f, d_K, h(O), d_{CM,O}(X_1(N))] for a single minimizing order O of conductor f, 
// fundamental discriminant d_K, and class number h(O). 

// NOTE: Takes into account Type1, Typ2, and Exceptional N to increase speed

// NOTE: smallest N for which this does not necessarily calculate the exact value of d_{CM}(X_1(N))
// is N = 50450400; see dcm_exact checker below

dcm_over_nonmax_orders := function(N)

    if is_of_Type1(N) then 
        return [1,-3,1,EulerPhi(N)/3];

    elif is_of_Type2(N) then
        return [1,-4,1,EulerPhi(N)/2];

    elif (N in exceptional_N) then
        for pair in exceptions_to_type_2 do
            if N eq pair[3] then
                return [pair[1],pair[2], 1, EulerPhi(N)/2];
            end if;
        end for;
        
    else
        PhiN := EulerPhi(N);

    	CondFundiscT0h := [cond_disc_list_allO[1][1][1], cond_disc_list_allO[1][1][2],T0(cond_disc_list_allO[1][1][1], cond_disc_list_allO[1][1][2], 1, N),1];
    	for i in [1..#cond_disc_list_allO[1]] do
    		if CondFundiscT0h[3] gt T0(cond_disc_list_allO[1][i][1], cond_disc_list_allO[1][i][2], 1, N) then//f. d_K,...
    			CondFundiscT0h:= [cond_disc_list_allO[1][i][1],cond_disc_list_allO[1][i][2],T0(cond_disc_list_allO[1][i][1], cond_disc_list_allO[1][i][2], 1, N),1];
            end if;
    	end for;

    	if (CondFundiscT0h[3] eq 1) or (CondFundiscT0h[3] eq PhiN) then
    		return [CondFundiscT0h[1], CondFundiscT0h[2], CondFundiscT0h[4], CondFundiscT0h[3]];

        else
    		h0 := CondFundiscT0h[3]; // upper bound for h_{minimizing Disc}
    		h := 2;
    		while h le h0 and h le 100 do
    			for pair in cond_disc_list_allO[h] do
    				if T0(pair[1], pair[2], 1, N) * h lt CondFundiscT0h[3] * CondFundiscT0h[4] then
    				    CondFundiscT0h := [pair[1], pair[2], T0(pair[1], pair[2], 1, N), h];
                        if CondFundiscT0h[3] * CondFundiscT0h[4] eq PhiN then //NEW 
                            return [CondFundiscT0h[1], CondFundiscT0h[2], CondFundiscT0h[4], CondFundiscT0h[3]*CondFundiscT0h[4]];
                        end if;
    				end if;
    			end for;
    			h:=h+1;
    		end while;
    	end if;
    end if;

	return [CondFundiscT0h[1], CondFundiscT0h[2], CondFundiscT0h[4], CondFundiscT0h[3]*CondFundiscT0h[4]];
end function;



// dcm_all_minimizing_orders : given natural number N > 1, minimizes d_{CM,O}(X_1(N)) over imaginary
// quadratic orders O of class number up to 100. Returns list [dcm, orders],
// where dcm is this minimum d_{CM,O}(X_1(N)) over such orders O and orders is complete sequence of sequences 
// [f, d_K, h(O)] for all minimizing orders O of class number up to 100, where f is the conductor, 
// d_K the fundamental discriminant, and h(O) is the class number of O

// note: smallest N for which this does not necessarily calculate the exact value of d_{CM}(X_1(N))
// is N = 50450400; see dcm_exact checker below

dcm_all_minimizing_orders := function(N)

    if is_of_Type1(N) then 
        return [*EulerPhi(N)/3, [[1,-3,1]]*];

    elif is_of_Type2(N) then
        return [*EulerPhi(N)/3, [[1,-4,1]]*];

    elif (N in exceptional_N) then
        orders := [];
        for pair in exceptions_to_type_2 do
            if N eq pair[3] then
                Append(~orders,[pair[1],pair[2],1]);
            end if;
        end for;
        return [* EulerPhi(N)/2, orders *];
        
    else
        PhiN := EulerPhi(N);

        dcm := T0(cond_disc_list_allO[1][1][1],cond_disc_list_allO[1][1][2],1,N); 
        for i in [1..#cond_disc_list_allO[1]] do
            if T0(cond_disc_list_allO[1][i][1], cond_disc_list_allO[1][i][2], 1, N) lt dcm then
                dcm := T0(cond_disc_list_allO[1][i][1], cond_disc_list_allO[1][i][2], 1, N);
            end if;
        end for;

        h0 := dcm; // h0 = upper bound for h_{minimizing Disc}, dcm here as h(O)=1 for above loop
        orders := []; // initialize sequence of minimizing orders

        h:=1;
        while h le h0 and h le 100 do
            for pair in cond_disc_list_allO[h] do
                if T0(pair[1], pair[2], 1, N) * h lt dcm then
                    dcm := T0(pair[1], pair[2], 1, N) * h; // resetting dcm 
                    orders := [[pair[1],pair[2],h]]; // resetting sequence of minimizing orders
                elif T0(pair[1], pair[2], 1, N) * h eq dcm then
                    Append(~orders,[pair[1],pair[2],h]); // appending minimizing orders
                end if;
            end for;
            h:=h+1;
        end while;

    end if;
    return [* dcm, orders *];
end function;



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Return to Guaranteeing a Sporadic CM Point on X_1(N)
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////



// loading sequence
// further_bads_X0_X1 = sequence of N for which we have not guaranteed a sporadic CM point on X_1(N) 
// using Frey-Faltings with upper bound on d_{CM}(X_1(N)) from Thm 5.1 (using any imaginary quadratic 
// discriminant D satisfying the Heegner hypothesis) and lower bound on 
// \frac{\gamma}{2} from JKS04

    // load 'further_bads_X0_X1.m'; 



// generating sequence
// hyper_bads_X1 : N in further_bads_X0_X1 such that X_1(N) is still not determined to have a sporadic CM point
// by computing d_{CM}(X_1(N)) exactly and comparing to lower bound on the gonality of X_1(N). 

    // hyper_bads_X1 := [N : N in further_bads_X0_X1 | dcm_over_nonmax_orders(N)[4] gt ((119*EulerPhi(N) * psi_from_fact(N, Factorization(N))) / 48000)];

    // SetOutputFile("hyper_bads_X1.m");
    // print hyper_bads_X1;
    // UnsetOutputFile();


// NOTE: Size of further_bads_X0_X1 lowered by 357 to 297 to get hyper_bads_X1, 
// with largest N in hyper_bads_X1 being 720

// NOTE: working over non-maximal orders removes 6 
// additional values: 450, 540, 840, 860, 900, 1080, compared to 
// only minimizing over maximal orders



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Checking Exactness of d_{CM}(X_1(N)) Calculations
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////



// dcm_exact_checker : given natural N, determines if the dcm value obtained from 
// dcm_over_nonmax_orders function is exact (returns true) rather than possibly just an upper bound 
// (returns false). We do this by determining if there is an order O with [f,d_K] = [cond, fun_disc_K] in 
// an imaginary quadratic field K such that 
// f^2*d_K < -4 and (T^o(O,N) * 2 / phi(N))*h(O) <= 100. 

// NOTE: Using this function, we find that the first N for which we are not guaranteed 
// to be computing d_{CM}(X_1(N)) exactly is 50450400

dcm_exact_checker := function(N)
    if is_of_Type1(N) or is_of_Type2(N) then
        return true;

    else
        for h in [1..100] do
            for order in cond_disc_list_allO[h] do
                if order[1]^2*order[2] lt -4 then 
                    if (T0(order[1],order[2],1,N) * 2/ EulerPhi(N)) * h le 100 then
                        return true;
                    end if;
                end if;
            end for;
        end for;
    end if; 
    return false;
end function; 




//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Guaranteeing NO Sporadic CM Point on X_1(N) for bad N
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////



// have exact gonality(X_1(N)) for N <= 40 and upper bounds for 
// N <= 250 by Derickx, van Hoeij. 
// Here we create list no_sporadic_CM_X1 of values of N for which we find that 
// d_{CM}(X_1(N)) >= gonality(X_1(N))

// declaring sequence
// gonality_upper_bds : Nth element is upper bound on gonality(X_1(N))

gonality_upper_bds := [1,1,1,1,1,1,1,1,1,1,
2,1,2,2,2,2,4,2,5,3,
4,4,7,4,5,6,6,6,11,6,
12,8,10,10,12,8,18,12,14,12,
22,12,24,15,18,19,29,16,21,15,
24,21,37,18,30,24,30,31,46,24,
49,36,36,32,42,30,58,36,44,36,
66,32,70,51,40,45,60,42,82,48,
54,58,90,48,72,64,70,60,104,48,
84,66,80,83,90,56,123,63,90,60,
133,72,139,84,96,105,150,72,156,90,
114,96,167,90,132,105,126,120,144,96,
132,139,140,120,125,96,211,112,154,126,
225,120,180,156,144,144,246,132,253,144,
184,189,210,128,210,184,168,171,291,120,
299,180,216,180,240,168,323,234,234,184,
264,162,348,210,240,240,365,192,260,216,
270,231,392,210,240,240,290,274,420,192,
429,252,310,264,342,240,360,276,288,270,
478,224,488,328,336,252,508,240,519,240,
374,382,420,288,420,398,396,336,450,288,
583,351,420,396,462,288,480,445,444,360,
504,342,651,384,360,444,675,360,687,396,
480,420,711,336,552,435,520,432,748,384,
761,396,486,465,504,420,630,480,574,375];



// generating sequence 
// no_sporadic_CM_X1 = sequence of all N such that, using above bounds and our exact d_{CM}(X_1(N)) 
// calculations, we can provably say X_1(N) has no sporadic CM points


    // load "hyper_bads_X1.m";

    // no_sporadic_CM_X1 := [1];

    // for N in [n : n in [2..250] | n in hyper_bads_X1] do
    // 	if dcm_over_nonmax_orders(N)[4] ge gonality_upper_bds[N] then
    // 		Append(~no_sporadic_CM_X1, N);
    // 	end if;
    // end for;

    // SetOutputFile("no_sporadic_CM_X1.m");
    // print no_sporadic_CM_X1;
    // UnsetOutputFile();

