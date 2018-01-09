(*
 *
 *
 * 256-bit RSA Encryption
 * Sam Lushtak
 * 4/17/17
 *
 *)

(*
 * For clarity purposes, set interface to display larger number of digits
 * than default.
 *)
Control.Print.intinfDepth := 1000;

(*
 * Make quot, rem infix operators, as they will be used frequently instead 
 * of div, mod.
 *)
infix 7 quot rem;

(*
 * Redeclare standard arithmetic operators to work IntInf.int type to be used
 * throughout this project. Note that in cases where we need to work with 
 * normal int values, we will need to use awk expressions such as Int.-(x,y).
 *
 * Function quotRem is unique to IntInf.int data type, and returns ordered pair
 * containing both the quotient and remainder more efficiently than calling
 * quot and rem separately.
 *)
val op +    = IntInf.+;
val op -    = IntInf.-;
val op *    = IntInf.*;
val op quot = IntInf.quot;
val op rem  = IntInf.rem;
val op <    = IntInf.<;
val op <=   = IntInf.<=;
val quotRem = IntInf.quotRem;
val fromInt = IntInf.fromInt;
val toInt   = IntInf.toInt;

(*
 * Hardcode IntInf.int values for constants to help SML type inferencing system
 * resolve function types.
 *)
val zero    = fromInt 0;
val one     = fromInt 1;
val two     = fromInt 2;
val three   = fromInt 3;

(*
 * 8-bit random generator
 *)
fun randomIntInf gen bits =
        let
            fun randomBits gen b =
                    let
                        val top = case b of
                                      1 =>   1
                                    | 2 =>   3
                                    | 3 =>   7
                                    | 4 =>  15
                                    | 5 =>  31
                                    | 6 =>  63
                                    | 7 => 127
                                    | 8 => 255
                                    | _ =>   0;
                    in
                        fromInt(Random.randRange(0,top) gen)
                    end;
            fun mult256 x = IntInf.<<(x, Word.fromInt 8);
        in
            if Int.<=(bits,8)
               then randomBits gen bits
               else randomBits gen 8 +
                    mult256(randomIntInf gen (Int.-(bits,8)))
        end;

(*
 * Function for finding the mod-m multiplicative inverse of u. Will return 
 * SOME a, with 0 <= a < m, if ua mod m = 1, will return NONE if there is 
 * no such a. Implementation uses a variant of Euclid's algorithm for finding
 * greatest common divisors.
 *)
fun inverseMod (u,m) =
        let
            (*
             * Invariant: There are constants b and d
             * satisfying
             *     x = au+bm  and  y = cu+dm.
             * If ever x=1, then 1 = au+bm, and a
             * is the inverse of u, mod m.
             *)
            fun extendedEuclid(x,y,a,c) =
                if x = zero
                   then NONE
                else if x = one
                   then SOME (if a < zero
                                 then a + m
                                 else a)
                else let
                         val (q,r) = quotRem(y,x);
                     in
                         extendedEuclid(r,x,c - a * q,a)
                     end;
        in
            extendedEuclid(u,m,one,zero)
        end;

(* 
 * Recursively computes b^e mod n, using principle that b^e = (b^(e/2))^2 
 * to efficiently calculate large exponents.
 *)
fun powerMod (b,e,n) =
	let
		fun squareMod (k,n) = k * k rem n;
	in
		if e = zero then
				one
			else if ((zero < e) andalso ((e rem two) = zero)) then
				squareMod (powerMod (b,e quot 2,n), n)
			else
				(squareMod (powerMod (b,e quot 2,n), n) * b) rem n
	end;	

(* 
 * Functions to convert between ints and their base-n list representations
 *)
fun block (n,m:IntInf.int) =
  		if (m > zero) then
   			(m rem n)::(block (n,(m quot n)))
   		else
   			[];

fun unblock (n,[]) = zero
  | unblock (n,(x::xs)) = x + (n * unblock(n,xs));


(* 
 * Convert a string to/from a list of integers, which is then represented
 * as a base-256 number.
 *)
fun messageToIntInf str = 
	let
		val strAsIntList = map (fromInt o ord) (explode str)
	in
		unblock ((fromInt 256),strAsIntList)
	end;

fun intInfToMessage encoded = 
	let
		val encodedBlocked = block (256,encoded)
		val toChars = map (chr o toInt) encodedBlocked
	in
		implode toChars
	end;

(* 
 * Encrypt integer m, such that m < n, using key (e,n).
 *)
fun rsaEncode (e,n) m = powerMod (m,e,n);

(* Take a string and encode/decode it, producing a single IntInf value 
 * encrypting message contained in that string. 
 *)
fun encodeString (e,n) str = 
	let
		val strAsNumber = messageToIntInf str
		val strAsIntList = block (n,strAsNumber)
	in
		unblock (n,(map (rsaEncode (e,n)) strAsIntList))
	end;

fun decodeString (e,n) encodedInt =
	let
		val chunkList = block (n,encodedInt)
		val decodedList = map (rsaEncode (e,n)) chunkList
		val intInfMessage = unblock (n,decodedList)
	in
		intInfToMessage intInfMessage
	end;

(* 
 * Create random number generator using arbitrary seed. 
 *)
val seed = (47,42);
val generator = Random.rand seed; 

(*
 * Find very large ("industrial strength") prime. To do so, create a 
 * pseudorandom number using generator and check 20 random values of a to see
 * if a^p mod p = a. Though not a guarantee, this makes it very likely that
 * the generated number is prime.
 *)
fun generateLessThan generator p numBits = 
	let
		val x = randomIntInf generator numBits
	in
		if (x < p) then
			x
		else
			generateLessThan generator p numBits
	end

fun primeCheck p generator numBits n = 
	let
		val a = generateLessThan generator p numBits
	in
		if (n = 0) then
			true
		else if (n > 0 andalso ((powerMod (a,p,p)) = a)) then
			primeCheck p generator numBits (n-1)
		else
			false
	end;
		
fun industrialStrengthPrime generator numBits = 
	let
		val p = randomIntInf generator numBits
		val startVal = 20
	in
		if (primeCheck p generator numBits startVal) then
			p
		else
			industrialStrengthPrime generator numBits
	end;

(* 
 * Generate RSA keys.
 *)
fun newRSAKeys generator numBits = 
	let
		val p = industrialStrengthPrime generator numBits
		val q = industrialStrengthPrime generator numBits
		val n = p * q
		val phi = (p - one) * (q - one)
		val d = generateLessThan generator n numBits
	in
		if (inverseMod (d,phi) = NONE) then
			newRSAKeys generator numBits
		else
			((valOf (inverseMod(d,phi)),n),(d,n))
	end;

(* 
 * Use the following to crack encryption.
 *)
fun allFactors x current = 
	if (x quot current < two) then
		[]
	else if (x rem current = zero) then
		current::(x div current)::(allFactors x (current + one))
	else
		allFactors x (current + one);

fun member _ []      = false
  | member e (x::xs) = e=x orelse (member e xs);

fun uniquify []      = []
  | uniquify (x::xs) =
    if member x xs
      then uniquify xs
      else x::(uniquify xs);

fun crack (e,n) = 
	let
		val factors = uniquify (allFactors n 2)
		val p = List.hd factors
		val q = List.last factors
		val phi = (p - one) * (q - one) 
	in
		Option.valOf (inverseMod(e,phi))
	end;



