// This code is for computing a list of discriminants of imaginary quadratic orders of 
// class number up to 100. 



// load list of fundamental discriminants of class numbers up to 100 by Watkins.
// ith element is a list of abs values of all fundamental discriminants of class
// number i.

load "classnum_disc_list.m";


// h0_calc : given (f,d_K,h_K) = (conductor, fundamental discriminant, class # of K) 
// for order O of disc d=f^2*d_K of im quadratic field K, returns 
// h(O) = h(f^2*(-d_K)) = (h(d_K)/w) * Phi_K(f)

hO_calc := function(f, d_K, h_K) //f>1
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

    if f eq 1 then
        return h_K;
    else 
        P := (f*h_K*w)/w_K;
        F := Factorization(f);
        for pair in F do
            P := P * (1 - KroneckerSymbol(d_K, pair[1]) / pair[1]);
        end for;
        return P;
    end if;
end function;



// phi_bound : given conductor f, gives lower bound on Phi(f) 
// l(f) = 0 for f=1
// l(f) = f/( 1.79*log(log(f)) + 3/(log(log(f))) )

phi_bound := function(f)
    if f eq 1 then
        return 0;
    elif f ge 2 then
        return f/( 1.79*Log(Log(f)) + 3/(Log(Log(f))) );
    end if;
end function;



// create list

// set h_max (for our purposes, 100, but could use <=100)

h_max := 100;

// set d_max as largest abs value of fundamental discriminant of class number at most h

d_max := 1;

for h in [1..h_max] do
    if classnum_disc_list[h][#classnum_disc_list[h]] gt d_max then
        d_max := classnum_disc_list[h][#classnum_disc_list[h]];
    end if;
end for;



// initialize list as list of 100 lists, where we will put in the orders
// of each class number up to 100

 cond_disc_list_allO := [**];

for i in [1..100] do
    Append(~cond_disc_list_allO,[**]);
end for;


// run through algorithm to obtain ALL imaginary quadratic orders 
// of class number up to 100.
// List generated has ith entry the full list of pairs [f,d_K] = [conductor, 
// discriminant_K] for imaginary quadratic orders of class number i

// note : the classnum_disc_list is consisting of absolute values of discriminants,
// so I try to make that clear in the notation instead of confronting my regrets head-on

    // start_time := Cputime();

    // for h_K in [1..h_max] do
    //     for abs_d_K in classnum_disc_list[h_K] do
    //         f:=1;

    //         w_K := 2;
    //         if -abs_d_K eq -4 then
    //             w_K := 4;
    //         elif -abs_d_K eq -3 then
    //             w_K := 6;
    //         end if;

    //         w := w_K;

    //         while (h_K*w/w_K)*phi_bound(f) le h_max do
    //             h := hO_calc(f,-abs_d_K,h_K);
    //             if h le h_max then
    //                 Append(~cond_disc_list_allO[Integers() ! h],[f,-abs_d_K]);
    //             end if;
    //             f := f+1;
    //             w := 2;
    //         end while;
    //     end for;
    // end for;

    // end_time := Cputime();
    // print "done. time taken: ", end_time-start_time;

    // SetOutputFile("cond_disc_list_allO.m");
    // print cond_disc_list_allO;
    // UnsetOutputFile();