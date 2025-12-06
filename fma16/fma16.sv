// ==== DISCLAIMER ====
// For the sake of transparency, some generative AI was used to help me clean up some parts of the code and help debug some problems I had. -Ryan
// Other specific things I had it help me with:
/*
 - fadd: The case block; formatting
 - fadd: the guard|round|sticky block near the end
 - had help figuring out a difficulty with an old fadd2 solution; old solution only considered Xs==Zs, but A and B must be picked based on Exp and mantissa too; helped application of negr/negz
 - help attempting to diagnose fma off-by-1 problems
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
   int exptemp; //signed intermediary exponent
   logic [6:0] exp_sum; //exponent sum
   logic [6:0] exp_norm; //exponent normalized
   logic [4:0] Re; //final exponent

   logic [10:0] Rm; //normalized significand
   logic [9:0] Rf; //stored fraction

   logic [15:0] p_add;
   logic NX_add, NX_mul;  // inexact flag for add and mul path

   logic [4:0] Ae_add, Be_add;
   logic [10:0] Asig_add, Bsig_add;
   logic [13:0] Aext_add, Bext_add;
   logic [4:0] dexp_add;
   logic [13:0] Baligned_add;
   logic [14:0] SumExt_add;
   logic [13:0] NormExt_add;
   logic [4:0] Eres_add;
   logic [10:0] Mant_add; //1 + 10 fractional bits
   logic guard_add, roundb_add, sticky_add, sticky2_add, sticky_all_add, guard_mul, round_mul, sticky_mul;
   logic [11:0] Mant12_add, Mant12_mul;
   logic [10:0] MantFinal_add, MantFinal_mul;
   logic [4:0] Efinal_add, Efinal_mul;
   logic signA_add, signB_add;
   logic [14:0] DiffExt_add;
   logic [13:0] SubMag_add;
   logic [3:0] sh_add;
   logic signX_eff, signZ_eff;
   logic [4:0] Xexp_add;
   logic [9:0] Xfrac_add;
   logic [10:0] Xsig_src;
   logic Xs_src;
   logic [13:0] Xext_Base, Zext_Base;
   logic lsb_add, inc_add, lsb_sub, inc_sub, lsb_mul, inc_mul;
   logic inexact_add;
   logic [15:0] x_abs, y_abs, z_abs;

   logic rm_rz;   // round toward zero
   logic rm_rne;  // round to nearest, ties to even
   logic rm_rp;   // round toward +inf
   logic rm_rn;   // round toward -inf

   always_comb begin
      rm_rz  = (roundmode == 2'b00);
      rm_rne = (roundmode == 2'b01);
      rm_rp  = (roundmode == 2'b10);
      rm_rn  = (roundmode == 2'b11);
   end

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

   //sign of product
   assign Ps = Xs ^ Ys;

   //significand product
   assign Pm = Xsig*Ysig;

   //fma_1: was experiencing alot of underflow errors, which I think is from the exponent sum being negative when exp_sum is calculated, 
   //but exp_sum is unsigned, so we should treat negative exponents as zero
   //fma_1: still getting 3 odd off-by-1 errors that i cant seem to get rid of so im going to skip it for now and come back to it

   always_comb begin
      // Signed exponent sum
      exptemp = Xe + Ye - BIAS;

      if (Pm == 22'd0) begin
         // exact zero product
         Rm = 11'd0;
         exp_norm= 7'd0;
         guard_mul = 1'b0;
         round_mul = 1'b0;
         sticky_mul = 1'b0;
      end else if (Pm[21]) begin
         // product mantissa in [2,4) -> normalize with +1 to exponent
         if (exptemp + 1 < 0) begin
            // underflow after normalization
            Rm = 11'd0;
            exp_norm = 7'd0;
            guard_mul = 1'b0;
            round_mul = 1'b0;
            sticky_mul = (Pm != 22'd0);
         end else begin
            // keep top 11 bits as mantissa
            Rm = Pm[21:11]; // 1.xxxxx xxxxx (11 bits)
            exp_norm = exptemp + 1;

            // GRS from lower bits of Pm
            guard_mul = Pm[10];
            round_mul = Pm[9];
            sticky_mul = |Pm[8:0];
         end
      end else begin
         // product mantissa in [1,2)
         if (exptemp < 0) begin
            // underflow
            Rm = 11'd0;
            exp_norm = 7'd0;
            guard_mul = 1'b0;
            round_mul = 1'b0;
            sticky_mul = (Pm != 22'd0);
         end else begin
            Rm = Pm[20:10];
            exp_norm = exptemp;

            guard_mul = Pm[9];
            round_mul = Pm[8];
            sticky_mul = |Pm[7:0];
         end
      end
   end

   //must normalize produict : if pm[21]==1 then shift right and raise exp
   //fma_1: need to round last, no rounding x*y; (exact x*y) + exact z -> then round

   //keep low 5 bits of exp
   assign Re = exp_norm[4:0];

   //Rm[10] ios the hidden 1, Rm[9:0] are the frac bits
   assign Rf = Rm[9:0];

   //16 bit result: p=x*y when mul=1, else p=x, return p
   logic [15:0] p_mul;

   //fmul results
   always_comb begin
      // inexact for the product
      NX_mul = guard_mul | round_mul | sticky_mul;

      Mant12_mul = {1'b0, Rm};     // 1 + 10 frac bits -> 12 bits
      lsb_mul    = Rm[0];

      // Rounding increment for mul
      inc_mul = 1'b0;

      // RZ: truncate
      if (rm_rz) begin
         inc_mul = 1'b0;

      // RNE: guard && (round | sticky | lsb)
      end else if (rm_rne) begin
         inc_mul = guard_mul && (round_mul | sticky_mul | lsb_mul);

      // RP: toward +inf (increment if positive and inexact)
      end else if (rm_rp) begin
         inc_mul = (~Ps) & NX_mul;

      // RN: toward -inf (increment if negative and inexact)
      end else begin // rm_rn
         inc_mul = Ps & NX_mul;
      end

      if (inc_mul)
         Mant12_mul = Mant12_mul + 12'd1;

      // possible carry out
      if (Mant12_mul[11]) begin
         MantFinal_mul = Mant12_mul[11:1];
         Efinal_mul    = Re + 5'd1;
      end else begin
         MantFinal_mul = Mant12_mul[10:0];
         Efinal_mul    = Re;
      end
   end

   assign p_mul = {Ps, Efinal_mul, MantFinal_mul[9:0]};

   // ====== fadd stuff ======
   //we want to make a general x + z for positive, same-sign, normalized numbers (fadd_0 and fadd_1)

   //idea to fix fma round by 1 error: find a case, and build Xext_base from Pm rather than

   logic tiny_prod_fma;

   always_comb begin
      // reuse exptemp and Pm
      tiny_prod_fma = 1'b0;
      if (mul && add && (Pm != 22'd0)) begin
         if (Pm[21]) begin
            tiny_prod_fma = (exptemp + 1 < 0);
         end else begin
            tiny_prod_fma = (exptemp < 0);
         end
      end
   end

   logic [10:0] Rm_fma;
   logic g_fma, r_fma, s_fma;
   logic [21:0] Ptmp;

   always_comb begin
      // Defaults
      p_add  = x;     // pass-through if not doing add
      NX_add = 1'b0;

      if (add) begin
         // ========= Choose X operand (product or original x) =========
         if (mul) begin
            // FMA path: (+- X*Y) +- Z  (always fused)
            Xs_src    = Ps;
            Xexp_add  = Re;
            Xfrac_add = Rm[9:0];
            Xsig_src  = Rm;
            Xext_Base = {Rm, guard_mul, round_mul, sticky_mul};
         end else begin
            // Pure add path: use original x
            Xs_src    = Xs;
            Xexp_add  = Xe;
            Xfrac_add = Xm;
            Xsig_src  = {1'b1, Xm};
            Xext_Base = {1'b1, Xm, 3'b000};
         end

         // ========= Effective signs after optional negations =========
         signX_eff = Xs_src ^ negr;
         signZ_eff = Zs    ^ negz;

         // Z mantissa extended with 3 low zeros
         Zext_Base = {1'b1, Zm, 3'b000};

         // ========= Exponent compare: choose A (larger) and B (smaller) =========
         if ((Xexp_add > Ze) || ((Xexp_add == Ze) && (Xfrac_add >= Zm))) begin
            Ae_add   = Xexp_add;
            Aext_add = Xext_Base;
            Be_add   = Ze;
            Bext_add = Zext_Base;
            signA_add= signX_eff;
            signB_add= signZ_eff;
         end else begin
            Ae_add   = Ze;
            Aext_add = Zext_Base;
            Be_add   = Xexp_add;
            Bext_add = Xext_Base;
            signA_add= signZ_eff;
            signB_add= signX_eff;
         end

         // ========= Align B to A with sticky =========
         dexp_add = Ae_add - Be_add;

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

         // ========= Same-sign: addition path =========
         if (signA_add == signB_add) begin
            SumExt_add = {1'b0, Aext_add} + {1'b0, Baligned_add};

            if (SumExt_add[14]) begin
               NormExt_add = SumExt_add[14:1]; // shift right
               Eres_add    = Ae_add + 5'd1;
            end else begin
               NormExt_add = SumExt_add[13:0];
               Eres_add    = Ae_add;
            end

            Mant_add    = NormExt_add[13:3]; // 11 bits = 1 + 10 frac
			guard_add   = NormExt_add[2];
			roundb_add  = NormExt_add[1];
			sticky2_add = NormExt_add[0]; // already includes aligned sticky via Baligned[0]

			// For the NX flag, *any* discarded bit counts:
			NX_add = guard_add | roundb_add | sticky_add | sticky2_add;

			Mant12_add = {1'b0, Mant_add};
			lsb_add    = Mant_add[0];

			// Rounding increment (same-sign add)
			inc_add = 1'b0;

			if (rm_rz) begin
				// round toward zero: truncate
				inc_add = 1'b0;

			end else if (rm_rne) begin
				// RNE: guard && (roundb | sticky2 | lsb)
				// NOTE: use sticky2_add only, NOT sticky_add,
				// because sticky_add is already folded into NormExt_add.
				inc_add = guard_add && (roundb_add | sticky2_add | lsb_add);

			end else if (rm_rp) begin
				// round to +inf
				inc_add = (~signA_add) & NX_add;

			end else begin
				// round to -inf
				inc_add =  signA_add & NX_add;
			end

            if (inc_add) begin
               Mant12_add = Mant12_add + 12'd1;
            end

            if (Mant12_add[11]) begin
               MantFinal_add = Mant12_add[11:1];
               Efinal_add    = Eres_add + 5'd1;
            end else begin
               MantFinal_add = Mant12_add[10:0];
               Efinal_add    = Eres_add;
            end

            p_add = {signA_add, Efinal_add, MantFinal_add[9:0]};

         end else begin
            // ========= Different-sign: subtraction path =========
            DiffExt_add = {1'b0, Aext_add} - {1'b0, Baligned_add};

            if (DiffExt_add == 15'd0) begin
               MantFinal_add = 11'd0;
               Efinal_add    = 5'd0;
               NX_add        = sticky_add;
               p_add         = 16'h0000;
            end else begin
               SubMag_add = DiffExt_add[13:0];

               if      (SubMag_add[13]) sh_add = 4'd0;
               else if (SubMag_add[12]) sh_add = 4'd1;
               else if (SubMag_add[11]) sh_add = 4'd2;
               else if (SubMag_add[10]) sh_add = 4'd3;
               else if (SubMag_add[9])  sh_add = 4'd4;
               else if (SubMag_add[8])  sh_add = 4'd5;
               else if (SubMag_add[7])  sh_add = 4'd6;
               else if (SubMag_add[6])  sh_add = 4'd7;
               else if (SubMag_add[5])  sh_add = 4'd8;
               else if (SubMag_add[4])  sh_add = 4'd9;
               else if (SubMag_add[3])  sh_add = 4'd10;
               else                     sh_add = 4'd11;

               NormExt_add = SubMag_add << sh_add;

               if (Ae_add > sh_add)
                  Eres_add = Ae_add - sh_add;
               else
                  Eres_add = 5'd0;

               Mant_add    = NormExt_add[13:3];
				guard_add   = NormExt_add[2];
				roundb_add  = NormExt_add[1];
				sticky2_add = NormExt_add[0];

				// For NX, again, any discarded bit counts:
				NX_add = guard_add | roundb_add | sticky_add | sticky2_add;

				Mant12_add = {1'b0, Mant_add};
				lsb_sub    = Mant_add[0];

				// Rounding increment (different-sign / subtraction)
				inc_sub = 1'b0;

				if (rm_rz) begin
					// round toward zero
					inc_sub = 1'b0;

				end else if (rm_rne) begin
					// RNE: guard && (roundb | sticky2 | lsb_sub)
					inc_sub = guard_add && (roundb_add | sticky2_add | lsb_sub);

				end else if (rm_rp) begin
					// round to +inf
					inc_sub = (~signA_add) & NX_add;

				end else begin
					// round to -inf
					inc_sub =  signA_add & NX_add;
				end

               if (inc_sub) begin
                  Mant12_add = Mant12_add + 12'd1;
               end

               if (Mant12_add[11]) begin
                  MantFinal_add = Mant12_add[11:1];
                  Efinal_add    = Eres_add + 5'd1;
               end else begin
                  MantFinal_add = Mant12_add[10:0];
                  Efinal_add    = Eres_add;
               end

               p_add = {signA_add, Efinal_add, MantFinal_add[9:0]};
            end
         end
      end // if (add)
   end // always_comb

   //=====top level select=====

   logic [15:0] p;
   logic [3:0] flags_next;

   always_comb begin
      // default
      p = x;
      flags_next = 4'b0000;

      if (mul && add) begin
         // fused FMA: (+-X*Y) +- Z
         p          = p_add;
         flags_next = {3'b000, NX_add};
      end else if (mul) begin
         // mul only
         p          = p_mul;
         flags_next = {3'b000, NX_mul};
      end else if (add) begin
         // add only
         p          = p_add;
         flags_next = {3'b000, NX_add};
      end

      result = p;
      flags = flags_next;
   end

endmodule

