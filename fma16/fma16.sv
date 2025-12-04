// ==== DISCLAIMER ====
// For the sake of transparency, some generative AI was used to help me clean up some parts of the code and help debug some problems I had. -Ryan
// Other specific things I had it help me with:
/*
 - fadd: The case block; formatting
 - fadd: the guard|round|sticky block near the end
 - had help figuring out a difficulty with an old fadd2 solution; old solution only considered Xs==Zs, but A and B must be picked based on Exp and mantissa too; helped application of negr/negz
 - how to start with the fma stuff for milestone 3; idea to embed the mult block in the add block
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
logic signA_add, signB_add;
logic [14:0] DiffExt_add;
logic [13:0] SubMag_add;
logic [3:0] sh_add;
logic signX_eff, signZ_eff;
logic [4:0] Xexp_add;
logic [9:0] Xfrac_add;
logic [10:0] Xsig_src;
logic Xs_src;



always_comb begin
	//Defaults
	p_add = x; // pass-through if not a recognized add
	NX_add = 1'b0;

	//handle add, no negation, same sign (fadd_0 / fadd_1)
	if (add) begin
		// in pure add mode (mul=0) : use x -> we pass on the mul block
		//in fma mode (mul=1) : use product x*y -> use the mul block as well
		if (mul) begin
			//use the normalized product stuff (Rm/Re/Ps) as the "new" X
			Xexp_add = Re;
			Xfrac_add = Rm[9:0];
			Xsig_src = Rm;
			Xs_src = Ps; // sign of product
		end else begin
			//use the original x as X
			Xexp_add = Xe;
			Xfrac_add = Xm;
			Xsig_src = {1'b1, Xm};
			Xs_src = Xs;
		end

		signX_eff = Xs_src ^ negr; //negate product
		signZ_eff = Zs ^ negz;

		if ((Xexp_add > Ze) || ((Xexp_add == Ze) && (Xfrac_add >=Zm))) begin
			Ae_add = Xexp_add;
			Asig_add = Xsig_src;
			Be_add = Ze;
			Bsig_add = {1'b1, Zm};
			signA_add = signX_eff;
			signB_add = signZ_eff;
		end else begin
			Ae_add = Ze;
			Asig_add = {1'b1, Zm};
			Be_add = Xexp_add;
			Bsig_add = Xsig_src;
			signA_add = signZ_eff;
			signB_add = signX_eff;
		end

		//extend significands with 3 low bits for guard/round/sticky
		Aext_add = {Asig_add, 3'b000};  //11 + 3 = 14 bits
		Bext_add = {Bsig_add, 3'b000};

		// exp difference (nonnegative because Ae is the larger)
		dexp_add = Ae_add - Be_add;


		// Align B to A with sticky
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

		//=====Same sign vs different sign===
		if (signA_add==signB_add) begin
			SumExt_add = {1'b0, Aext_add} + {1'b0, Baligned_add};

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
			p_add ={signA_add, Efinal_add, MantFinal_add[9:0]};

		end else begin
			// --- different sign addition (fadd_2)
			//by construction A is larger, so A - B>=0
			DiffExt_add = {1'b0, Aext_add} - {1'b0, Baligned_add};
			//check if there is exact cancellation
			if (DiffExt_add==15'd0) begin
				MantFinal_add=11'd0;
				Efinal_add=5'd0;
				NX_add=sticky_add; //only true if there was an alignment sticky
				p_add=16'h0000; //final pass
			end else begin
				//magnitude of difference -> ignore msb of DiffExt_add
				SubMag_add = DiffExt_add[13:0];

				//check for leading 0
				if(SubMag_add[13]) sh_add = 4'd0;
					else if (SubMag_add[12]) sh_add = 4'd1;
					else if (SubMag_add[11]) sh_add = 4'd2;
					else if (SubMag_add[10]) sh_add = 4'd3;
					else if (SubMag_add[9]) sh_add = 4'd4;
					else if (SubMag_add[8]) sh_add = 4'd5;
					else if (SubMag_add[7]) sh_add = 4'd6;
					else if (SubMag_add[6]) sh_add = 4'd7;
					else if (SubMag_add[5]) sh_add = 4'd8;
					else if (SubMag_add[4]) sh_add = 4'd9;
					else if (SubMag_add[3]) sh_add = 4'd10;
					else  sh_add = 4'd11;

					NormExt_add= SubMag_add << sh_add;

					if (Ae_add > sh_add) begin
						Eres_add = Ae_add - sh_add;
					end else begin
						Eres_add = 5'd0;
					end
					
					Mant_add = NormExt_add[13:3];
					guard_add = NormExt_add[2];
					roundb_add = NormExt_add[1];
					sticky2_add = NormExt_add[0];

					sticky_all_add= sticky_add | guard_add | roundb_add | sticky2_add;
					NX_add = sticky_all_add;

					MantFinal_add = Mant_add;
					Efinal_add = Eres_add;

					p_add = {signA_add, Efinal_add, MantFinal_add[9:0]};
			end
		end
	end
end

//=====top level select=====

logic [15:0] p;
logic [3:0] flags_next;

always_comb begin
	// default
	p = x;
	flags_next = 4'b0000;

	if (mul && add) begin
		//fma: (+-X*Y) +-Z (product x*y fed into adder with z)
		p = p_add;
		flags_next = {3'b000, NX_add};
	end else if (mul) begin
		p = p_mul;
		flags_next = 4'b0000;
	end else if (add) begin
		p=p_add;
		flags_next = {3'b000, NX_add};
	end

	result = p;
	flags = flags_next;
end


   // stubbed ideas for instantiation ideas
   
   // fmaexpadd expadd(.Xe, .Ye, .XZero, .YZero, .Pe);
   // fmamult mult(.Xm, .Ym, .Pm);
   // fmasign sign(.OpCtrl, .Xs, .Ys, .Zs, .Ps, .As, .InvA);
   // fmaalign align(.Ze, .Zm, .XZero, .YZero, .ZZero, .Xe, .Ye, .Am, .ASticky, .KillProd);
   // fmaadd add(.Am, .Pm, .Ze, .Pe, .Ps, .KillProd, .ASticky, .AmInv, .PmKilled, .InvA, .Sm, .Se, .Ss);
   // fmalza lza (.A(AmInv), .Pm(PmKilled), .Cin(InvA & (~ASticky | KillProd)), .sub(InvA), .SCnt);

 
endmodule

