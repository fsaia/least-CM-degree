// The aim of this code is to compute, for integers M, N >= 2 with M | N, the least degree over Q(zeta_M) 
// of a CM point on the modular curve X(M,N). We denote the degree by d_{CM}^{Q(zeta_M}}(X(M,N)). 

// We then use this to try to guarantee the existence of a sporadic CM point on X(M,N), or else
// to try to prove there can be no such point on this curve. 


//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Computing d_{O,CM}^{Q(zeta_M}}(X(M,N)) for 
// a given order O
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////


// T_Tilde_PrimePower : given conductor f = [\mathcal{O_K} : \mathcal{O}] of an order \mathcal{O} in an 
// imaginary quadratic field K, d_K the discriminant of K, l a rational prime, and a and b non-negative 
// integers, computes \tilde{T}(\mathcal{O},l^a, l^b) as in Thm 4.1 of BC19

T_Tilde_PrimePower := function(f,d_K,l,a,b)
    w_K := 2;
    if d_K eq -4 then
        w_K := 4;
    elif d_K eq -3 then
        w_K := 6;
    end if;

    w := 2;
    if f eq 1 then
        w := w_K;
    end if;
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
// imaginary quadratic field K, d_K the discriminant of K, and M|N positive integers with N>1,
// computes T\mathcal{O},M,N) as in Thm 4.1 of BC19

T := function(f,d_K,M,N) // ONLY use N > 1, M|N
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
        return 1;
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
// via Thm 6.6 in BC19

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



// m_leq2_calc : given conductor f of an order \mathcal{O} in an imaginary quadratic field K, d_K the 
// discriminant of K, returns m := max integer b for which there is an \mathcal{O}-CM elliptic curve over
// Q(f) with a Q(f)-rational cyclic 2^b isogeny
// note: this is prop 6.4 in BC19 with l=2

m_leq2_calc := function(f,d_K) 
    c := Valuation(f,2);

    if f^2*d_K eq -4 then 
        return 2;

    elif (f mod 2 eq 0) and ( ((KroneckerSymbol(d_K,2) eq 1) or (KroneckerSymbol(d_K,2) eq -1)) ) then
        if c eq 1 then
            return 1;
        else
            return 2*c-2;
        end if;

    elif (f^2*d_K ne -4) and (KroneckerSymbol(d_K,2) eq 0) then 
        if c eq 0 then
            return 1;
        elif c ge 1 then
            if Valuation(d_K,2) eq 2 then
                return 2*c;
            elif Valuation(d_K,2) eq 3 then
                return 2*c+1;
            end if;
        end if; 

    end if;
end function; 



// M_leq2_calc : given conductor f of an order \mathcal{O} in an imaginary quadratic field K, d_K the 
// discriminant of K, returns M := sup over integers b for which there is an \mathcal{O}-CM elliptic curve over
// K(f) with a K(f)-rational cyclic 2^b isogeny
// note: this is prop 6.4 in BC19 with l=2

M_leq2_calc := function(f,d_K)
    c := Valuation(f,2);
    
    if f^2*d_K eq -4 then 
        return 2;
    else 
        if (f mod 2 eq 0) and (KroneckerSymbol(d_K,2) eq 1) then
            return Infinity();
        elif (f mod 2 eq 0) and (KroneckerSymbol(d_K,2) eq -1) then
            return 2*c;
        elif KroneckerSymbol(d_K,2) eq 0 then
            return 2*c+1;
        else
            return "You shouldn't be seeing this!";
        end if;
    end if;
end function; 



// T0_Meq2_Neq2b_need2 : given conductor f of an order \mathcal{O} in an imaginary quadratic field K, 
// d_K the discriminant of K, and b a positive integer, returns true if 
// T^\circ(\mathcal{O},2,2^b) = 2*T(\mathcal{O},2,2^b), returns
// false if T^\circ(\mathcal{O},2,2^b) = T(\mathcal{O},2,2^b)
// note: this is thm 8.5 and prop 8.6 from BC19

T0_Meq2_Neq2b_need2 := function(f,d_K,b)
    if f^2*d_K eq -4 then 
        if b eq 1 then
            return false;
        elif b gt 1 then
            return true;
        end if;

    elif f^2*d_K lt -4 then
        m := m_leq2_calc(f,d_K);
        M := M_leq2_calc(f,d_K);

        if b le m then
            return false;

        elif (b eq 2) and ((m eq 1) and (M gt 1)) then
            return true;

        elif (m+1 lt b) and (b le M) then
            return true;

        elif ((3 le m+1) and (m+1 eq b)) and (b le M) then
            return false;

        elif ((b gt M) and (M eq m)) and (m ge 1) then
            return false;

        elif ((b gt M) and (M gt m)) and (m ge 1) then 
            return true;

        end if;
    end if;
end function;



// T0 : given conductor f = [\mathcal{O_K} : \mathcal{O}] of an order \mathcal{O} in an imaginary
// quadratic field K, d_K the discriminant of K, and M|N positive integers with N>1, computes 
// T^\circ(\mathcal{O},M,N) - the least degree over Q(f) of a number field F for which there is an 
// \mathcal{O}-CM elliptic curve over F and an injective group hom Z/MZ x Z/NZ --> E(F)
// using section 7 of BC19 for M=1, section 8 for M>1. (thm 1.4)

// NOTE: M=1 case same as in least_degreesX1.m

T0 := function(f,d_K,M,N) 

    if N mod M ne 0 then
        return "N is not divisible by M!";
    end if;

    need2 := false;
    if M eq 1 then
        FN := Factorization(N);
        for pair in FN do
            if T0_PrimePower_need2(f,d_K,pair[1],pair[2]) eq true then
                need2 := true;
                break;
            end if;
        end for;
        if need2 eq true then
            return 2*T(f,d_K,M,N); 
        else
            return T(f,d_K,M,N); 
        end if;
    end if;

    if M ne 2 then 
        return 2*T(f,d_K,M,N);
    end if;

    if f^2 * d_K mod 2 ne 0 then
        return 2*T(f,d_K,M,N);
    end if;

    FN := Factorization(N);
    for pair in FN do
        if pair[1] eq 2 then
            if T0_Meq2_Neq2b_need2(f,d_K,pair[2]) eq true then//
                need2 := true;
            break;
            end if;
        
        else //Note: in this case, since we're looking at T0(O, l^a, l^b) w/ l>2 and M=2, we have T0(O, l^a, l^b)=T0(O,1,l^b), so reduces to code for X_1.
            if T0_PrimePower_need2(f,d_K,pair[1],pair[2]) eq true then
                need2 := true;
                break;
            end if;
        end if; 
    end for; 

    if need2 eq true then
        return 2*T(f,d_K,M,N); 
    else
        return T(f,d_K,M,N); 
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



// d_OCM_XMN : given conductor f = [\mathcal{O_K} : \mathcal{O}] of an order \mathcal{O} in an imaginary
// quadratic field K, d_K the discriminant of K, and M|N positive integers with N>1, computes 
// d_{O,CM}^{Q(zeta_M)}(X(M,N)) - the least degree over Q(\zeta_M) of a number field F for which there is an 
// \mathcal{O}-CM elliptic curve over F and an injective group hom Z/MZ x Z/NZ --> E(F) 

// NOTE: This function is not used below, as the list of orders we loop over is already sorted by 
// class number, and the factor 
// [Q(f) : Q] = (2/w_K)*f*Prod*h_K in case f>1, h_K in case f=1
// below is equal to the class number of O. 

d_OCM_XMN := function(f,d_K,M,N)
    
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
            return T0(f,d_K,M,N)*h_K / EulerPhi(M);
        else
            Prod := 1;
            for pair in Factorization(f) do
                Prod := Prod*(1-KroneckerSymbol(d_K,pair[1])*(1/pair[1]));
            end for;
            return ( (T0(f,d_K,M,N)*(2/w_K)*f*Prod*h_K) / EulerPhi(M) );
        end if;
    end if;
end function; 



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Minimizing d_{O,CM}^{Q(zeta_M)}(X(M,N)) over orders O of 
// class number <=100
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////



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
    if N lt 7 then
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




// dcm_over_nonmax_orders : give naturals M | N, minimizes d_{O,CM}^{Q(zeta_M)}(X(M,N)) over imaginary 
// quadratic orders O of class number up to 100. Returns sequence 
// [f, d_K, h(O), d_{O,CM}^{Q(zeta_M)}(X(M,N))] for a single minimizing order O of conductor f, 
// fundamental discriminant d_K, and class number h(O).

// NOTE: Takes into account Type1, Typ2, and Exceptional N in M=1 case to increase speed

// NOTE: throughout function, dcm refers to dcm over Q. At the end, we divide by phi(M) to get dcm over 
// Q(zeta_M)

dcm_over_nonmax_orders := function(M,N)

    if M eq 1 then // Checks for shortcuts in computing d_cm(X_1(N))
        if is_of_Type1(N) eq true then
            return [1,-3,1,EulerPhi(N)/3];
        elif (is_of_Type2(N) eq true) then
            return [1,-4,1,EulerPhi(N)/2];
        elif  (N in exceptional_N) eq true then
            for pair in exceptions_to_type_2 do
                if N eq pair[3] then
                    return [pair[1],pair[2], 1, EulerPhi(N)/2];
                end if;
            end for;
        end if;
    end if;

    CondFundiscT0h := [cond_disc_list_allO[1][1][1], cond_disc_list_allO[1][1][2],T0(cond_disc_list_allO[1][1][1], cond_disc_list_allO[1][1][2], M, N),1];
    for i in [1..#cond_disc_list_allO[1]] do
        if CondFundiscT0h[3] gt T0(cond_disc_list_allO[1][i][1], cond_disc_list_allO[1][i][2], M, N) then
            CondFundiscT0h:= [cond_disc_list_allO[1][i][1],cond_disc_list_allO[1][i][2],T0(cond_disc_list_allO[1][i][1], cond_disc_list_allO[1][i][2], M, N),1];
        end if;
    end for;

    phi_M := EulerPhi(M);

    if CondFundiscT0h[3] eq phi_M then
        return [CondFundiscT0h[1], CondFundiscT0h[2], CondFundiscT0h[4], 1];

    else
        h0 := CondFundiscT0h[3]; // upper bound for h_{minimizing Disc}
        h := 2;
        while h le h0 and h le 100 do
            for pair in cond_disc_list_allO[h] do
                if T0(pair[1], pair[2], M, N) * h lt CondFundiscT0h[3] * CondFundiscT0h[4] then
                    CondFundiscT0h := [pair[1], pair[2], T0(pair[1], pair[2], M, N), h];
                    if T0(pair[1], pair[2], M, N) * h eq phi_M then
                        return [CondFundiscT0h[1], CondFundiscT0h[2], CondFundiscT0h[4], CondFundiscT0h[3]];
                    end if;
                end if;
            end for;
            h:=h+1;
        end while;
    end if;
    return [CondFundiscT0h[1], CondFundiscT0h[2], CondFundiscT0h[4], CondFundiscT0h[3]*CondFundiscT0h[4] / EulerPhi(M)];
end function;




// dcm_all_minimizing_orders : give naturals M | N, minimizes d_{O,CM}^{Q(zeta_M)}(X(M,N)) over imaginary 
// quadratic orders O of class number up to 100. Returns list [d_{O,CM}^{Q(zeta_M)}(X(M,N)),orders] 
// where dcm is this minimum d_{O,CM}^{Q(zeta_M)}(X(M,N)) over such orders O and orders is complete 
// sequence of sequences [f, d_K, h(O)] for all minimizing orders O of class number up to 100, where 
// f is the conductor, d_K the fundamental discriminant, and h(O) is the class number of O

// NOTE: Takes into account Type1, Typ2, and Exceptional N in M=1 case to increase speed

// NOTE: throughout function, dcm refers to dcm over Q. At the end, we divide by phi(M) to get dcm over 
// Q(zeta_M)

dcm_all_minimizing_orders := function(M,N)

    if M eq 1 then // Checks for shortcuts in computing d_cm(X_1(N))
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
        end if;
    end if;

    dcm := T0(cond_disc_list_allO[1][1][1], cond_disc_list_allO[1][1][2], M, N);
    for i in [1..#cond_disc_list_allO[1]] do
        if T0(cond_disc_list_allO[1][i][1], cond_disc_list_allO[1][i][2], M, N) lt dcm then
            dcm := T0(cond_disc_list_allO[1][i][1], cond_disc_list_allO[1][i][2], M, N);
        end if;
    end for;

    h0 := dcm; // h0 = upper bound for h_{minimizing Disc}, dcm here as h(O)=1 for above loop
    orders := []; // initialize sequence of minimizing orders

    h := 1;
    while h le h0 and h le 100 do
        for pair in cond_disc_list_allO[h] do
            if T0(pair[1], pair[2], M, N) * h lt dcm then
                dcm := T0(pair[1], pair[2], M, N) * h; // resetting dcm 
                orders := [[pair[1],pair[2],h]]; // resetting sequence of minimizing orders
            elif T0(pair[1], pair[2], M, N) * h eq dcm then
                Append(~orders,[pair[1],pair[2],h]); // appending minimizing orders
            end if;
        end for;
        h:=h+1;
    end while;
    return [* dcm, orders *];
end function;



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Return to Guaranteeing a Sporadic CM Point on X(M,N)
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////



// phi_from_fact: Given natural N, factorization of N (list of pairs (p,a)), computes phi(N) 

phi_from_fact := function(N,F)
    P := N;
    for i in [1..#F] do
        P := P*(1-1/(F[i][1]));
    end for;
    return P;
end function;


// psi_from_fact: Given natural N, factorization of N (list of pairs (p,a)), computes psi(N)

psi_from_fact := function(N,F)
    M := 1;
        for i in [1..#F] do
            M := M * (F[i][1]+1)*F[i][1]^(F[i][2]-1);
        end for;
    return M;
end function;



// loading sequence 
// further_bads_XMN : sequence of N which we could not guarantee
// a sporadic CM point on X(M,N) for all M|N using Frey-Faltings with 
// the upper bound on d_{CM}^{Q(zeta_M)}(X_(M,N)) from Thm 5.1 (using any imaginary quadratic 
// discriminant D satisfying the Heegner hypothesis) and lower bound on 
// \frac{\gamma}{2} from JKS04

    // load "further_bads_XMN.m";



// generating sequence
// hyper_badsXMN : N in further_bads_XMN such that X(M,N) is still not determined to have a sporadic CM point
// by minimizing d_{O,CM}(X(M,N)) over orders O of class number up to 100 (using dcm_over_nonmax_orders)
// comparing to lower bound on the gonality of X(M,N). 

    // hyper_bads_XMN := [];

    // for N in further_bads_XMN do
    //     FN := Factorization(N);
    //     for M in Divisors(N) do 
    //         if dcm_over_nonmax_orders(M,N)[4] gt (RealField(10) ! ((119*M*phi_from_fact(N,FN)*psi_from_fact(N,FN))/48000)) then
    //             Append(~hyper_bads_XMN, [M,N]);
    //         end if;
    //     end for;
    // end for;

    // SetOutputFile("hyper_bads_XMN.m");
    // print hyper_bads_XMN;
    // UnsetOutputFile();


// NOTE: Size of hyper_bads_XMN is 480. There are 297 distinct values of N appearing, with the highest
// being N=720. 



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Checking Exactness of d_{CM}(X_(M,N)) Calculations
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////



// dcm_exact_checker : given naturals M | N, determines if the dcm value obtained from 
// dcm_over_nonmax_orders function is exact (returns true) rather than possibly just an upper bound 
// (returns false). We do this by checking for an order O with [f,d_K] = [cond, fun_disc_K] in 
// im quad fld K such that f^2*d_K < -4 and T^o(O,M,N)*h(O) <= 100. 

// We use that phi(N)/2 | T^o(O,M,N) for disc(O)<-4, so suffices to check (T^o(O,M,N) * 2 / phi(N))*h(O) <= 100 
// (which we did for the X_1(N) = X(1,N) computations; there is such an order for all N < 50450400). 

dcm_exact_checker := function(M,N)
    if M eq 1 then
        if N lt 50450400 then
            return true;
        elif is_of_Type1(N) or is_of_Type2(N) then
            return true;
        end if; 
    end if; 

    for h in [1..100] do
        for order in cond_disc_list_allO[h] do
            if order[1]^2*order[2] lt -4 then 
                if ((T0(order[1],order[2],M,N) * 2 * h) / EulerPhi(N)) le 100 then 
                    return true;
                end if;
            end if;
        end for;
    end for;

    return false;
end function; 



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Guaranteeing NO Sporadic CM Point on X(M,N) for bad (M,N)
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////



// have exact gonality(X_1(N)) for N <= 40 and upper bounds for 
// N <= 250 by Derickx, van Hoeij:

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



// Here we create list no_sporadic_CM_XMN of values of N for which we find that 
// d_{CM}(X(M,N)) >= gonality(X(M,N))

// generating sequence 
// no_sporadic_CM_XMN = sequence of all N such that, using above bounds and *exact* d_{CM}(X(M,N)) 
// calculations (dcm_exact_checker shows exactness for all relevant pairs), 
// we can provably say X(M,N) has no sporadic CM points

    // load "hyper_bads_XMN.m";

    // no_sporadic_CM_XMN:=[];

    // for pair in [pair : pair in hyper_bads_XMN | pair[2] le 250] do
    //     if dcm_over_nonmax_orders(pair[1],pair[2])[4] ge (gonality_upper_bds[pair[2]] * EulerPhi(pair[1]) * pair[1]) then
    //         Append(~no_sporadic_CM_XMN, pair);
    //     end if; 
    // end for;

    // SetOutputFile("no_sporadic_CM_XMN.m");
    // print no_sporadic_CM_XMN;
    // UnsetOutputFile();


