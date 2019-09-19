// Knowing there are finitely many N for which the modular curve X_1(N) may not
// have a sporadic CM point, this code is for checking such N further,
// with a stronger inequality, to see if we can guarantee a sporadic point. 

// Note: We get same list of further_bads for X_0(N) by comparison of d_{CM}(X_1(N)) and d_{CM}(X_0(N))


// "trivial" constant above which sporadic CM pts on X_1(N) guaranteed

C := 102641930;  


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
// modulo p for all primes p dividing N (henceforth: -D is Heegner for N). Then, test if 
// inequality which guarantees sporadic CM points on X_1(N) (coming from Frey-Faltings) 
// is satisfied, yielding output "bad". Otherwise, "good". (Note: yells if discriminant is 
// not found in list of imaginary quad discriminants used, disc_ClassNumber_list here)

// More specifically: N is bad if it does not satisfy the inequality 
// (h(-D(N)) ge (119*psi_from_fact(N)/48000))
// which guarantees a sporadic CM point.

// note: we are only checking the least such D here; we perform further checks below

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
	if found_disc eq false then
		return "discriminant -D not in list";
	elif (h ge (119*psi_from_fact(N,F)/48000)) then
		return "bad";
	else
		return "good";
	end if;
end function;
		

// check_for_bads: given naturals low <= high, searches for largest bad natural between low 
// and high. If found, returns largest bad and time taken for search, otherwise prints no
// primes found and time taken for search. Will yell if is_bad runs into problem 
// finding a discriminant. 

// for original search, checked in ranges like this as multiple computers were utilized

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


// using above functions, we find that there are 689 bads, with the highest bad being 4290

bads := [N : N in [1..4290] | is_bad(N) eq "bad"];


// further_check1: given natural N, checks if inequality to guarantee sporadic points would be satisfied
// with h = 1. If not, there is no chance this strategy could work, output "no chance". Otherwise, 
// we look to see if an imaginary quadratic class number one discriminant satisfies the 
// Heegner hypothesis for N, telling us we do have sporadic points on X_1(N), output "good". If no
// such discriminant works, output "check further", as some higher h could still work. 

// note: this function narrows our list of bads down by 7 to 682, with 285 fully checked 
// and 397 needing to be checked further

classnum_one_D_list := [-3,-4,-7,-8,-11,-19,-43,-67,-163];

further_check1 := function(N)
	F := Factorization(N);
	R1 := RealField(20);
	if (1 ge (119*psi_from_fact(N,F)/48000)) then
		return "no chance";
    else
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

bads_checked := [N : N in bads | further_check1(N) eq "no chance"]; // size is 285
bads_to_check := [N : N in bads | further_check1(N) eq "check further"]; // size is 397


// further_check: given natural N, looks for discriminant up to highD for which Heegner hypothesis
// is satisfied *and* sporadic points on X_1(N) are guaranteed using Frey-Faltings inequality with
// h corresponding to this discriminant. If so, output "good". Otherwise, output "bad".

// Note1: highD determined by finding largest h such that set of N in bads_to_check such that the inequality 
// guaranteeing a sporadic CM point is satisfied with N and h is non-empty, and taking highD to be largest 
// -D among discriminants of im. quad. fields with class number up to h. 

// Note2: In reality, we lower the highest h value from 29 to 12 to quicken computations. We do this by noting that
// that for h >= 12, the set of N for which the inequality is satisfied with N and h is 
// small (3 or less). We check these N individually with further_check, with 
// highD as needed, and then either remove them from bads_to_check if good, or remove them 
// from bads_to_check and append to bads_checked if bad. 

// Note3: Another approach would be to determine the highest working h for
// N, and only check discriminants of fields with class number up to h, instead of looping over all
// discriminants up to highD for each N. This may seem nicer, but what is done is done. 

further_check := function(N)
	F := Factorization(N);
	highD := 19*937; // used 166147 before lowering h from 29 to 12.
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
            	if (h lt (119*psi_from_fact(N,F)/48000)) then
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

    //h=29: 4290 bad
    //h=28: 3990 bad
    //h=25: 3570 bad
    //h=17: 2310, 2520, 2820 bad
    //h=16: 2814 bad
    //h=14: 2100 bad
    //h=13: 2184 bad

individual_checks := [4290, 3990, 3570, 2310, 2520, 2820, 2814, 2100, 2184];
for i in individual_checks do
	Exclude(~bads_to_check, i);
	Append(~bads_checked, i);
end for;

    // h := 1;
    // R1 := RealField(20);
    // while ([N : N in bads_to_check | ( h lt ((119/48000)*psi_from_fact(N,Factorization(N))) )] ne []) do
    // 	h := h+1;
    // end while;
    // print h-1;

    // print [N : N in bads_to_check | ( h-1 lt ((119/48000)*psi_from_fact(N,Factorization(N))) )];


// We generate the sequence further_bads_X0_X1 : bads that have no hope of being determined to be good
// using the inequality coming from Frey-Faltings and our upper bound on d_{CM}(X_1(N)).
// This is the list of bads already fully checked by further_check1 or during the lowering
// of highD above, plus elements remaining in bads_to_check that are determined to be bad via further_check 

// From this, we get 654 total bads remaining, with the highest being 4290

    // further_bads_X0_X1 := bads_checked;

    // for N in bads_to_check do
    // 	if further_check(N) eq "bad" then
    //  		Append(~further_bads_X0_X1, N);
    //  	end if;
    // end for;

    // Sort(~further_bads_X0_X1);

    // SetOutputFile("further_bads_X0_X1.m");
    // print further_bads_X0_X1;
    // UnsetOutputFile();





