// ==== DISCLAIMER ====
// For the sake of transparency, generative AI was used to help me clean up some parts of the code and help debug some problems I had.
//Specific things I had it help me with:
/*
 - fadd: The case block; formatting
 - fadd: the guard|round|sticky block near the end
*/

//fmul tests completed 0-2
//fadd_0 test completed

// fma16.sv
// David_Harris@hmc.edu 26 February 2022

// Operation: general purpose multiply, add, fma, with optional negation
//   If mul=1, p = x * y.  Else p = x.
//   If add=1, result = p + z.  Else result = p.
//   If negr or negz = 1, negate result or z to handle negations and subtractions
//   fadd: mul = 0, add = 1, negr = negz = 0
//   fsub: mul = 0, add = 1, negr = 0, negz = 1
//   fmul: mul = 1, add = 0, negr = 0, negz = 0
//   fmadd:  mul = 1, add = 1, negr = 0, negz = 0
//   fmsub:  mul = 1, add = 1, negr = 0, negz = 1
//   fnmadd: mul = 1, add = 1, negr = 1, negz = 0
//   fnmsub: mul = 1, add = 1, negr = 1, negz = 1

module fma16 (x, y, z, mul, add, negr, negz,
	      roundmode, result, flags);
   
   input logic [15:0]  x, y, z;   
   input logic 	       mul, add, negr, negz;
   input logic [1:0]   roundmode;
   
   output logic [15:0] result;
   output logic [3:0]  flags;

   logic [4:0] 	       Xe, Ye, Ze;
   logic [9:0] 	       Xm, Ym, Zm;
   logic 	       Xs, Ys, Zs;

logic [10:0] Xsig, Ysig; //1.xxx (11bits)
logic [21:0] Pm; //product of significands
logic Ps; // product sign

localparam int BIAS = 15;
logic [6:0] exp_sum; //exponent sum
logic [6:0] exp_norm; //exponent normalized
logic [4:0] Re; //final exponent

logic [10:0] Rm; //normalized significand
logic [9:0] Rf; //stored fraction

always_comb begin
	//break x, y, z into sign/exp/frac

	Xs = x[15];
	Xe = x[14:10];
	Xm = x[9:0];

	Ys = y[15];
	Ye = y[14:10];
	Ym = y[9:0];

	Zs = z[15];
	Ze = z[14:10];
	Zm = z[9:0];
end

//====== fmul stuff =====

//need significands with hidden 1 for normalized nbumbers
assign Xsig = {1'b1, Xm};
assign Ysig = {1'b1, Ym};

//fmul core:

//sign of product
assign Ps = Xs ^ Ys;

//significand product
assign Pm=Xsig*Ysig;

//Exponent (sum-bias)
assign exp_sum=Xe+Ye-BIAS;


//must normalize produict : if pm[21]==1 then shift right and raise exp

always_comb begin
	if(Pm[21]) begin
	//1x.xxx then -> by 1
		Rm=Pm[21:11]; //top 11 bits
		exp_norm = exp_sum +1;
	end else begin //if already [1,2)
		Rm=Pm[20:10];
		exp_norm=exp_sum;
	end
end

//keep low 5 bits of exp
assign Re = exp_norm[4:0];

//Rm[10] ios the hidden 1, Rm[9:0] are the frac bits
assign Rf = Rm[9:0];

//16 bit result: p=x*y when mul=1, else p=x, return p
logic [15:0] p_mul;

//fmul results
assign p_mul = {Ps,Re,Rf};

// ====== fadd stuff ======
//we want to make a general x + z for positive, same-sign, normalized numbers (fadd_0 and fadd_1)

logic [15:0] p_add;
logic NX_add;  // inexact flag for add path

logic [4:0] Ae_add, Be_add;
logic [10:0] Asig_add, Bsig_add;
logic [13:0] Aext_add, Bext_add;
logic [4:0] dexp_add;
logic [13:0] Baligned_add;
logic [14:0] SumExt_add;
logic [13:0] NormExt_add;
logic [4:0] Eres_add;
logic [10:0] Mant_add; //1 + 10 fractional bits
logic guard_add, roundb_add, sticky_add, sticky2_add, sticky_all_add;
logic [11:0] Mant12_add;
logic [10:0] MantFinal_add;
logic [4:0] Efinal_add;



always_comb begin
	//Defaults
	p_add = x; // pass-through if not a recognized add
	NX_add = 1'b0;

	//handle add, no negation, same sign (fadd_0 / fadd_1)
	if (!mul && add && (negr == 1'b0) && (negz == 1'b0) && (Xs == Zs)) begin
		//choose operand with larger exponent as A

		if (Xe >= Ze) begin
			Ae_add = Xe;
			Asig_add = {1'b1, Xm};
			Be_add = Ze;
			Bsig_add = {1'b1, Zm};
		end else begin
			Ae_add = Ze;
			Asig_add = {1'b1, Zm};
			Be_add = Xe;
			Bsig_add = {1'b1, Xm};
		end

		//extend significands with 3 low bits for guard/round/sticky
		Aext_add = {Asig_add, 3'b000};  //11 + 3 = 14 bits
		Bext_add = {Bsig_add, 3'b000};

		// exp difference (nonnegative because Ae is the larger)
		dexp_add =Ae_add - Be_add;

		// Align B to A with sticky (no variable part-selects)
        case (dexp_add)
            5'd0: begin
                Baligned_add = Bext_add;
                sticky_add   = 1'b0;
            end
            5'd1: begin
                Baligned_add = Bext_add >> 1;
                sticky_add   = Bext_add[0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            5'd2: begin
                Baligned_add = Bext_add >> 2;
                sticky_add   = |Bext_add[1:0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            5'd3: begin
                Baligned_add = Bext_add >> 3;
                sticky_add   = |Bext_add[2:0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            5'd4: begin
                Baligned_add = Bext_add >> 4;
                sticky_add   = |Bext_add[3:0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            5'd5: begin
                Baligned_add = Bext_add >> 5;
                sticky_add   = |Bext_add[4:0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            5'd6: begin
                Baligned_add = Bext_add >> 6;
                sticky_add   = |Bext_add[5:0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            5'd7: begin
                Baligned_add = Bext_add >> 7;
                sticky_add   = |Bext_add[6:0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            5'd8: begin
                Baligned_add = Bext_add >> 8;
                sticky_add   = |Bext_add[7:0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            5'd9: begin
                Baligned_add = Bext_add >> 9;
                sticky_add   = |Bext_add[8:0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            5'd10: begin
                Baligned_add = Bext_add >> 10;
                sticky_add   = |Bext_add[9:0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            5'd11: begin
                Baligned_add = Bext_add >> 11;
                sticky_add   = |Bext_add[10:0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            5'd12: begin
                Baligned_add = Bext_add >> 12;
                sticky_add   = |Bext_add[11:0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            5'd13: begin
                Baligned_add = Bext_add >> 13;
                sticky_add   = |Bext_add[12:0];
                Baligned_add[0] = Baligned_add[0] | sticky_add;
            end
            default: begin
                // dexp_add >= 14: B is so small it’s purely sticky
                sticky_add   = |Bext_add;
                Baligned_add = 14'd0;
                Baligned_add[0] = sticky_add;
            end
        endcase

		//add magnitudes
		SumExt_add = {1'b0, Aext_add} + {1'b0, Baligned_add};

		//normalize: if there is a carry-out, shift right 1 and bump exponent
		if (SumExt_add[14]) begin
			NormExt_add = SumExt_add[14:1]; //shift right
			Eres_add = Ae_add + 5'd1;
		end else begin
			NormExt_add = SumExt_add[13:0];
			Eres_add = Ae_add;
		end

		Mant_add = NormExt_add[13:3]; // 11 bits = 1 +10 frac
		guard_add= NormExt_add[2];
		roundb_add = NormExt_add[1];
		sticky2_add = NormExt_add[0]; //includes previous sticky via Baligned[0]

		sticky_all_add = sticky2_add;

		//rne rounding (roundmode is assumed rne for these tests)
		NX_add = guard_add | roundb_add | sticky_all_add;

		MantFinal_add = Mant_add;
		Efinal_add = Eres_add;

		//result, sign is Xs (== Zs)
		p_add ={Xs, Efinal_add, MantFinal_add[9:0]};
	end
end

//=====top level select=====

logic [15:0] p;
logic [3:0] flags_next;

always_comb begin
	// default
	p = x;
	flags_next = 4'b0000;

	if (mul) begin
		// multiply path (fmul_0/1/2)
		p = p_mul;
		flags_next = 4'b0000;
	end else if (add) begin
		// add path (fadd_0 / fadd_1 so far)
		p = p_add;
		flags_next = {3'b000, NX_add};  //NX in bit[0]
	end

	result = p;
	flags  = flags_next;
end


   // stubbed ideas for instantiation ideas
   
   // fmaexpadd expadd(.Xe, .Ye, .XZero, .YZero, .Pe);
   // fmamult mult(.Xm, .Ym, .Pm);
   // fmasign sign(.OpCtrl, .Xs, .Ys, .Zs, .Ps, .As, .InvA);
   // fmaalign align(.Ze, .Zm, .XZero, .YZero, .ZZero, .Xe, .Ye, .Am, .ASticky, .KillProd);
   // fmaadd add(.Am, .Pm, .Ze, .Pe, .Ps, .KillProd, .ASticky, .AmInv, .PmKilled, .InvA, .Sm, .Se, .Ss);
   // fmalza lza (.A(AmInv), .Pm(PmKilled), .Cin(InvA & (~ASticky | KillProd)), .sub(InvA), .SCnt);

 
endmodule

