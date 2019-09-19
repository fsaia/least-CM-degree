// Knowing there are finitely many N for which the modular curve X(M,N) may not
// have a sporadic CM point for some M, this code is for checking such N further,
// with a stronger inequality, to see if we can guarantee a sporadic CM point for all M. 


// "trivial" constant C such that a sporadic CM point on X(M,N) is guaranteed
// for all M|N for all N >= C. 

C := 474059054;  


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


// is_bad: Given natural N, find least positive D such that -D is a quadratic residue 
// modulo p for all primes p dividing N. Then, test if inequality which guarantees 
// sporadic CM points on X(M,N) (coming from Frey-Faltings) is satisfied, yielding 
// output "bad". Otherwise, "good". (Note: yells if discriminant is not found in list 
// of imaginary quad discriminants used, disc_ClassNumber_list here)

// Again, N is bad if it does not satisfy the inequality 
// h(-D(N))<119*psi(N)/96000
// which guarantees a sporadic CM point.

is_bad := function(N)
	F := Factorization(N);
    	D := 2;
   	D_Found := false;
	while D_Found eq false do 
		D := D+1; 
  	  	if -D mod 4 eq 0 or -D mod 4 eq 1 then 
      		check := true; 
            for i in [1..#F] do
                if KroneckerSymbol(-D,F[i][1]) ne 1 then
                    check := false;
                end if;
            end for;
            if check eq true then
                D_Found := true;
            end if; 
        end if;
    end while;
    
    found_disc := false;
	for j in [1..#disc_ClassNumber_list] do
		if -D eq disc_ClassNumber_list[j][1] then
			h := disc_ClassNumber_list[j][2];
			found_disc := true;
			break;
		end if;
	end for;
	R1 := RealField(20);
	if found_disc eq false then
		return "discriminant -D not in list";
	elif h ge (119*psi_from_fact(N,F)/96000) then
		return "bad";
	else
		return "good";
	end if;
end function;
		

// check_for_bads: given naturals low <= high, searches for largest bad natural between low 
// and high. If found, returns largest bad and time taken for search, otherwise prints no
// primes found and time taken for search. Will yell if is_bad runs into problem 
// finding a discriminant. 

check_for_bads := function(low,high)
	start_time := Cputime();
 	j := high;
    while j ge low do
        if is_bad(j) eq "bad" then
            end_time := Cputime();
        	print "Done. Time taken", end_time - start_time;
            return "first bad found:",j;
            break;
        elif is_bad(j) eq "discriminant -D not in list" then
        	end_time := Cputime();
        	print "Done. Time taken", end_time - start_time;
        	return "discriminant -D not in list", j;
        	break;
        end if;
        j := j-1;
    end while;
	end_time := Cputime();
	print "Done. Time taken", end_time - start_time;
	return "no bads found";
end function; 


// using above functions, we find that there are 1436 bads, with the highest bad being 8580

bads := [N : N in [1..8580] | is_bad(N) eq "bad"];


// further_check1: given natural N, checks if inequality to guarantee sporadic points would be satisfied
// with h = 1. If not, there is no chance this strategy could work, output "No chance". Otherwise, 
// we look to see if an imaginary quadratic class number one discriminant satisfies the 
// Heegner hypothesis for N, telling us we do have sporadic points on X(M,N), output "good". If no
// such discriminant works, output "check further", as some higher h could still work. 

// note: this function narrows our list of bads down by 21 to 1415, with 567 fully checked 
// and 848 needing to be checked further

further_check1 := function(N)
	F := Factorization(N);
	R1 := RealField(20);
	if 1 ge (119*psi_from_fact(N,F)/96000) then
		return "no chance";
    else
    	classnum_one_D_list := [-3,-4,-7,-8,-11,-19,-43,-67,-163];
    	for D in classnum_one_D_list do
    		check := true;
    		for i in [1..#F] do
    			if (KroneckerSymbol(D,F[i][1]) ne 1) then
                    check := false;
                end if;
            end for;
            if check eq true then
            	return "good";
            	break;
            end if;
        end for;
        return "check further";
     end if;
end function; 


// we generate lists bads_checked of bads for which there is "No chance" from further_check1
// and bads_to_check for which we find we need to "check further" from further_check1

bads_checked := [N : N in bads | further_check1(N) eq "no chance"]; // size is 567
bads_to_check := [N : N in bads | further_check1(N) eq "check further"]; // size is 848


// further_check: given natural N, looks for discriminant up to highD for which Heegner hypothesis
// is satisfied *and* sporadic points on X(M,N) are guaranteed using Frey-Faltings inequality with
// h corresponding to this discriminant. If so, output "good". Otherwise, output "bad".

// Note1: highD was found by looking at largest h such that set of bad N such the inequality is satisfied
// with N and h is non-empty, and taking highD to be largest -D among discriminants of im. quad. fields 
// with class number up to h. 

// Note2: In fact, we lower the highest h value from 29 to 12 to quicken computations. We do this by noting 
// that for h >= 12, the set of N for which the inequality is satisfied with N and h is small (6 or less), so 
// we just check these N individually with further_check with highD as needed and then either
// remove them from bads_to_check if good, or remove them from bads_to_check and append to bads_checked if bad. 

// Note3: Another way to do this to speed things up would be to determine the highest working h for 
// N and only check discriminants of fields with class number up to h, instead of looping over all
// discriminants up to highD for each N. We chose to get by without this nicer method. 

further_check := function(N)
	F := Factorization(N);
	highD := 19*937; // used 166147 before lowering high h value from 29 to 12
    D := 3;
	while D le highD do
  	  	if -D mod 4 eq 0 or -D mod 4 eq 1 then 
      		check := true; 
            for i in [1..#F] do
                if KroneckerSymbol(-D,F[i][1]) ne 1 then
                    check := false;
                end if;
            end for;
            if check eq true then
            	for j in [1..#disc_ClassNumber_list] do
					if -D eq disc_ClassNumber_list[j][1] then
						h := disc_ClassNumber_list[j][2];
						break;
					end if;
				end for;
				R1 := RealField(20);
            	if h lt (119*psi_from_fact(N,F)/96000) then
            		return "good";
            	end if;
            end if; 
        end if;
        D := D+1;
    end while;
    return "bad";
end function;


// here is code we used to lower highD in further_check - see note2 above - preceded by notes 
// about the lowering itself

    // h=29 gives 8580 bad
    // h=28 gives 7980 bad
    // h=25 gives 7140, 7854 bad
    // h=24 gives 7410 bad
    // h=22 gives 6510 bad
    // h=21 gives 6090 bad
    // h=19 gives 6006 bad
    // h=17 gives 4620, 4830, 5040, 5250, 5640, 6726 bad
    // h=16 gives 5628 bad
    // h=15 gives 5418 bad
    // h=14 gives 3990, 4200, 4290, 4410, 4914 bad | 5478 good
    // h=13 gives 4368, 4818 bad | 5622, 5698 good

found_bad := [8580,7980,7140,7854,7410,6510,6090,6006,4620,4830,5040,5250,5640,6726,5628,5418,3990,4200,4290,4410,4914,4368,4818];
found_good := [5478,5622,5698];

for i in found_bad do
    Append(~bads_checked,i);
    Exclude(~bads_to_check,i);
end for;

for i in found_good do
    Exclude(~bads_to_check,i);
end for;


    // h := 1;
    // R1 := RealField(20);
    // while ([N : N in bads_to_check | (h lt (119*psi_from_fact(N,Factorization(N))/96000))] ne []) do
    // 	h := h+1;
    // end while;
    // print h-1;

    // print [N : N in bads_to_check | ((h-1) lt (119*psi_from_fact(N,Factorization(N))/96000))];


// We generate the sequence further_bads_XMN : sequence of bads that have no hope of being determined to be good
// using the inequality coming from Frey-Faltings and our upper bound on d_{CM}(X(M,N)).
// This is the list of bads already fully checked by further_check1 or during the lowering
// of highD above, plus elements remaining in bads_to_check that are determined to be bad via further_check 

// From this, we get 1350 total bads remaining, with the highest being 8580

    // further_bads_XMN := bads_checked;

    // for N in bads_to_check do
    // 	if further_check(N) eq "bad" then
    //  		Append(~further_bads_XMN, N);
    //  	end if;
    // end for;

    // Sort(~further_bads_XMN);

    // SetOutputFile("further_bads_XMN.m");
    // print further_bads_XMN;
    // UnsetOutputFile();





