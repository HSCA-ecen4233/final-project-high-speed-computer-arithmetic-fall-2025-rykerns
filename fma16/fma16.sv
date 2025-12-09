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
   
   input  logic [15:0] x, y, z;   
   input  logic        mul, add, negr, negz;
   input  logic [1:0]  roundmode;
   
   output logic [15:0] result;
   output logic [3:0]  flags;

   logic [4:0]  Xe, Ye, Ze;
   logic [9:0]  Xm, Ym, Zm;
   logic        Xs, Ys, Zs;

   logic [10:0] Xsig, Ysig; // 1.xxx (11bits)
   logic [21:0] Pm;         // product of significands
   logic        Ps;         // product sign

   localparam logic signed [6:0] BIAS = 7'd15;
   logic signed [6:0] exptemp;    // signed intermediary exponent
   logic signed [6:0] exp_sum;    // exponent sum (unused)
   logic signed [6:0] exp_norm;   // exponent normalized
   logic [4:0]        Re;         // final exponent

   logic [10:0] Rm; // normalized significand
   logic [9:0]  Rf; // stored fraction

   logic [15:0] p_add;
   logic        NX_add, NX_mul;  // inexact flag for add and mul path

   logic [4:0]  Ae_add, Be_add;
   logic [10:0] Asig_add, Bsig_add;
   logic [13:0] Aext_add, Bext_add;
   logic [4:0]  dexp_add;
   logic [13:0] Baligned_add;
   logic [14:0] SumExt_add;
   logic [13:0] NormExt_add;
   logic [4:0]  Eres_add;
   logic [10:0] Mant_add; // 1 + 10 fractional bits
   logic        guard_add, roundb_add, sticky_add, sticky2_add, sticky_all_add;
   logic        guard_mul, round_mul, sticky_mul;
   logic [11:0] Mant12_add, Mant12_mul;
   logic [10:0] MantFinal_add, MantFinal_mul;
   logic [4:0]  Efinal_add, Efinal_mul;
   logic        signA_add, signB_add;
   logic [14:0] DiffExt_add;
   logic [13:0] SubMag_add;
   logic [4:0]  sh_add;
   logic        signX_eff, signZ_eff;
   logic [4:0]  Xexp_add;
   logic [9:0]  Xfrac_add;
   logic [10:0] Xsig_src;
   logic        Xs_src;
   logic [13:0] Xext_Base, Zext_Base;
   logic        lsb_add, inc_add, lsb_sub, inc_sub, lsb_mul, inc_mul;
   logic        inexact_add;
   logic [15:0] x_abs, y_abs, z_abs;
   logic        sticky_carry_add;
   logic        sticky_round_add;  // combined sticky for RNE

   logic rm_rz;   // round toward zero
   logic rm_rne;  // round to nearest, ties to even
   logic rm_rp;   // round toward +inf
   logic rm_rn;   // round toward -inf

   // ========= Rounding-mode decode =========
   always_comb begin
      rm_rz  = (roundmode == 2'b00);
      rm_rne = (roundmode == 2'b01);
      rm_rp  = (roundmode == 2'b10);
      rm_rn  = (roundmode == 2'b11);
   end

   // ========= Break x, y, z into sign/exp/frac =========
   always_comb begin
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

   // ========= Classification of specials =========
   logic XZero, YZero, ZZero;
   logic XInf,  YInf,  ZInf;
   logic XNaN,  YNaN,  ZNaN;
   logic XsNaN, YsNaN, ZsNaN;

   always_comb begin
      XZero = (Xe == 5'd0)  && (Xm == 10'd0);
      YZero = (Ye == 5'd0)  && (Ym == 10'd0);
      ZZero = (Ze == 5'd0)  && (Zm == 10'd0);

      XInf  = (Xe == 5'h1F) && (Xm == 10'd0);
      YInf  = (Ye == 5'h1F) && (Ym == 10'd0);
      ZInf  = (Ze == 5'h1F) && (Zm == 10'd0);

      XNaN  = (Xe == 5'h1F) && (Xm != 10'd0);
      YNaN  = (Ye == 5'h1F) && (Ym != 10'd0);
      ZNaN  = (Ze == 5'h1F) && (Zm != 10'd0);

      // treat any non-zero NaN frac with MSB 0 as signaling
      XsNaN = XNaN && ~Xm[9];
      YsNaN = YNaN && ~Ym[9];
      ZsNaN = ZNaN && ~Zm[9];
   end

   // ========= Special-result path =========
   logic        special_case;
   logic [15:0] special_result;
   logic [3:0]  special_flags;   // {INV, OF, UF, NX}

   // canonical quiet NaN: sign=0, exp=all 1s, MSB of frac=1, rest 0
   localparam logic [15:0] QNAN = 16'h7E00;

   // Helper classification for product operand
   logic ProdZero, ProdInf;
   logic PInf, PZero;
   logic Psign_eff, Zsign_eff;
   logic ZInf_eff;

   // product classification for mul path
   assign ProdZero = mul && (XZero || YZero) && ~(XInf || YInf);
   assign ProdInf  = mul && (XInf || YInf) && ~(XZero || YZero);

   // Special-case handler: NaNs, 0*Inf, Inf±Inf, Inf±finite
   always_comb begin
      special_case   = 1'b0;
      special_result = 16'h0000;
      special_flags  = 4'b0000;

      // defaults for helper signals (avoid latches)
      PInf      = 1'b0;
      PZero     = 1'b0;
      Psign_eff = 1'b0;
      Zsign_eff = 1'b0;
      ZInf_eff  = 1'b0;

      // 1) signaling NaN present → qNaN, INV
      if (XsNaN || YsNaN || ZsNaN) begin
         special_case   = 1'b1;
         special_result = QNAN;
         special_flags  = 4'b1000; // INV=1
      end
      // 2) any quiet NaN → qNaN (no INV)
      else if (XNaN || YNaN || ZNaN) begin
         special_case   = 1'b1;
         special_result = QNAN;
         special_flags  = 4'b0000;
      end
      else begin
         // 3) 0 * Inf (in either order) → qNaN, INV
         if (mul && ((XZero && YInf) || (YZero && XInf))) begin
            special_case   = 1'b1;
            special_result = QNAN;
            special_flags  = 4'b1000;
         end
         else begin
            // Build P / Z classification and effective signs
            if (mul) begin
               // P is X*Y
               PInf      = ProdInf;
               PZero     = ProdZero;
               Psign_eff = (Xs ^ Ys) ^ negr; // Ps ^ negr
            end
            else begin
               // P is just X (pure add)
               PInf      = XInf;
               PZero     = XZero;
               Psign_eff = Xs ^ negr;
            end

            ZInf_eff  = ZInf;
            Zsign_eff = Zs ^ negz;

            if (add) begin
               // 4) Inf - Inf → qNaN, INV
               if (PInf && ZInf_eff && (Psign_eff != Zsign_eff)) begin
                  special_case   = 1'b1;
                  special_result = QNAN;
                  special_flags  = 4'b1000;
               end
               // 5) Inf + finite, finite + Inf, Inf + Inf same sign → Inf
               else if (PInf || ZInf_eff) begin
                  special_case = 1'b1;
                  if (PInf && !ZInf_eff) begin
                     special_result = {Psign_eff, 5'h1F, 10'd0};
                  end
                  else if (!PInf && ZInf_eff) begin
                     special_result = {Zsign_eff, 5'h1F, 10'd0};
                  end
                  else begin
                     // both Inf, same sign
                     special_result = {Psign_eff, 5'h1F, 10'd0};
                  end
                  special_flags = 4'b0000; // exact
               end
            end
            else if (mul && ProdInf) begin
               // 6) Pure multiply with Inf (already excluded 0*Inf above)
               special_case   = 1'b1;
               special_result = {(Xs ^ Ys), 5'h1F, 10'd0}; // Ps
               special_flags  = 4'b0000;
            end
         end
      end
   end

   // ========= fmul stuff =========

   // need significands with hidden 1 for normalized numbers
   assign Xsig = (Xe != 5'd0) ? {1'b1, Xm} : 11'd0;
   assign Ysig = (Ye != 5'd0) ? {1'b1, Ym} : 11'd0;

   // sign of product
   assign Ps = Xs ^ Ys;

   // significand product
   assign Pm = Xsig * Ysig;

   // normalize product mantissa + exponent
   always_comb begin
      // Signed exponent sum (7-bit)
      exptemp = $signed({2'b00, Xe}) + $signed({2'b00, Ye}) - BIAS;

      if (Pm == 22'd0) begin
         // exact zero product
         Rm        = 11'd0;
         exp_norm  = 7'sd0;
         guard_mul = 1'b0;
         round_mul = 1'b0;
         sticky_mul= 1'b0;

      end else if (Pm[21]) begin
         // product mantissa in [2,4) -> normalize with +1 to exponent
         if (exptemp + 7'sd1 < 7'sd0) begin
            // underflow after normalization
            Rm        = 11'd0;
            exp_norm  = 7'sd0;
            guard_mul = 1'b0;
            round_mul = 1'b0;
            sticky_mul= (Pm != 22'd0);
         end else begin
            // keep top 11 bits as mantissa
            Rm        = Pm[21:11];
            exp_norm  = exptemp + 7'sd1;

            // GRS from lower bits of Pm
            guard_mul = Pm[10];
            round_mul = Pm[9];
            sticky_mul= |Pm[8:0];
         end

      end else begin
         // product mantissa in [1,2)
         if (exptemp < 7'sd0) begin
            // underflow
            Rm        = 11'd0;
            exp_norm  = 7'sd0;
            guard_mul = 1'b0;
            round_mul = 1'b0;
            sticky_mul= (Pm != 22'd0);
         end else begin
            Rm        = Pm[20:10];
            exp_norm  = exptemp;

            guard_mul = Pm[9];
            round_mul = Pm[8];
            sticky_mul= |Pm[7:0];
         end
      end
   end

   // keep low 5 bits of exp
   assign Re = exp_norm[4:0];

   // Rm[10] is the hidden 1, Rm[9:0] are the frac bits
   assign Rf = Rm[9:0];

   // 16 bit result: p=x*y when mul=1 (mul-only path)
   logic [15:0] p_mul;

   // fmul results + rounding
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

   // ========= fadd / FMA add stuff =========

   logic tiny_prod_fma;

   always_comb begin
      tiny_prod_fma = 1'b0;
      if (mul && add && (Pm != 22'd0)) begin
         if (Pm[21]) begin
            tiny_prod_fma = (exptemp + 7'sd1 < 7'sd0);
         end else begin
            tiny_prod_fma = (exptemp < 7'sd0);
         end
      end
   end

   always_comb begin
      // Defaults for everything driven in this block to fix lint latch errors
      p_add      = x;        // pass-through if not doing add
      NX_add     = 1'b0;

      Xs_src     = 1'b0;
      Xexp_add   = 5'd0;
      Xfrac_add  = 10'd0;
      Xsig_src   = 11'd0;
      Xext_Base  = 14'd0;
      signX_eff  = 1'b0;
      signZ_eff  = 1'b0;
      Zext_Base  = 14'd0;

      Ae_add     = 5'd0;
      Aext_add   = 14'd0;
      Be_add     = 5'd0;
      Bext_add   = 14'd0;
      signA_add  = 1'b0;
      signB_add  = 1'b0;

      dexp_add   = 5'd0;
      Baligned_add = 14'd0;
      sticky_add = 1'b0;

      SumExt_add = 15'd0;
      NormExt_add= 14'd0;
      Eres_add   = 5'd0;
      Mant_add   = 11'd0;
      guard_add  = 1'b0;
      roundb_add = 1'b0;
      sticky2_add= 1'b0;

      Mant12_add    = 12'd0;
      lsb_add       = 1'b0;
      inc_add       = 1'b0;
      MantFinal_add = 11'd0;
      Efinal_add    = 5'd0;

      DiffExt_add = 15'd0;
      SubMag_add  = 14'd0;
      sh_add      = 5'd0;
      lsb_sub     = 1'b0;
      inc_sub     = 1'b0;

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

            // For normals: hidden 1; for exp=0 (zero/subnormal): treat as 0
            if (Xe != 5'd0) begin
               Xsig_src  = {1'b1, Xm};
               Xext_Base = {1'b1, Xm, 3'b000};
            end else begin
               Xsig_src  = 11'd0;
               Xext_Base = 14'd0;
            end
         end

         // ========= Effective signs after optional negations =========
         signX_eff = Xs_src ^ negr;
         signZ_eff = Zs    ^ negz;

         // Z mantissa extended with 3 low zeros; zero/denorm → 0
         if (Ze != 5'd0)
            Zext_Base = {1'b1, Zm, 3'b000};
         else
            Zext_Base = 14'd0;

         // ========= Exponent compare: choose A (larger) and B (smaller) =========
         if ((Xexp_add > Ze) || ((Xexp_add == Ze) && (Xfrac_add >= Zm))) begin
            Ae_add    = Xexp_add;
            Aext_add  = Xext_Base;
            Be_add    = Ze;
            Bext_add  = Zext_Base;
            signA_add = signX_eff;
            signB_add = signZ_eff;
         end else begin
            Ae_add    = Ze;
            Aext_add  = Zext_Base;
            Be_add    = Xexp_add;
            Bext_add  = Xext_Base;
            signA_add = signZ_eff;
            signB_add = signX_eff;
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

            // Normalize; when there is a carry, we shift right and must
            // fold the dropped bit (SumExt_add[0]) into sticky.
            if (SumExt_add[14]) begin
               NormExt_add = SumExt_add[14:1];   // (SumExt_add >> 1)[13:0]
               Eres_add    = Ae_add + 5'd1;
            end else begin
               NormExt_add = SumExt_add[13:0];
               Eres_add    = Ae_add;
            end

            Mant_add   = NormExt_add[13:3]; // 11 bits = 1 + 10 frac
            guard_add  = NormExt_add[2];
            roundb_add = NormExt_add[1];

            // Sticky bit below guard:
            //  - if no carry, just the lowest bit of NormExt
            //  - if carry, also OR in SumExt_add[0], the bit lost by the shift
            if (SumExt_add[14])
               sticky2_add = NormExt_add[0] | SumExt_add[0];
            else
               sticky2_add = NormExt_add[0];

            // Inexact if any bit below the LSB we keep is nonzero
            NX_add = guard_add | roundb_add | sticky2_add;

            Mant12_add = {1'b0, Mant_add};
            lsb_add    = Mant_add[0];

            // Rounding increment (same-sign add)
            inc_add = 1'b0;

            if (rm_rz) begin
               // round toward zero
               inc_add = 1'b0;

            end else if (rm_rne) begin
               // RNE: guard && (roundb | sticky2 | lsb_add)
               // sticky2_add now already includes the dropped carry bit when needed
               inc_add = guard_add && (roundb_add | sticky2_add | lsb_add);

            end else if (rm_rp) begin
               // round to +inf
               inc_add = (~signA_add) & NX_add;

            end else begin
               // round to -inf
               inc_add =  signA_add & NX_add;
            end

            if (inc_add)
               Mant12_add = Mant12_add + 12'd1;

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

               if      (SubMag_add[13]) sh_add = 5'd0;
               else if (SubMag_add[12]) sh_add = 5'd1;
               else if (SubMag_add[11]) sh_add = 5'd2;
               else if (SubMag_add[10]) sh_add = 5'd3;
               else if (SubMag_add[9])  sh_add = 5'd4;
               else if (SubMag_add[8])  sh_add = 5'd5;
               else if (SubMag_add[7])  sh_add = 5'd6;
               else if (SubMag_add[6])  sh_add = 5'd7;
               else if (SubMag_add[5])  sh_add = 5'd8;
               else if (SubMag_add[4])  sh_add = 5'd9;
               else if (SubMag_add[3])  sh_add = 5'd10;
               else                     sh_add = 5'd11;

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
               NX_add = guard_add | roundb_add | sticky2_add;

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
   end // always_comb (add/FMA)

   // ========= Top-level select with specials / OF / UF =========

   logic [15:0] p;
   logic [3:0]  flags_next;

   always_comb begin
      // default
      p          = x;
      flags_next = 4'b0000;

      if (special_case) begin
         // NaNs, 0*Inf, Inf±Inf, Inf±finite
         p          = special_result;
         flags_next = special_flags;
      end else begin
         // Finite-path result selection
         logic [15:0] p_core;
         logic        NX_core;
         logic        sign_core;
         logic [4:0]  exp_core;
         logic [9:0]  frac_core;
         logic        INV_finite, OF_finite, UF_finite, NX_finite;
         logic [15:0] p_finite;

         // default core: pass-through x (no operation)
         p_core  = x;
         NX_core = 1'b0;

         if (mul && add) begin
            // fused FMA: (+-X*Y) +- Z
            p_core  = p_add;
            NX_core = NX_add;
         end else if (mul) begin
            // mul only
            p_core  = p_mul;
            NX_core = NX_mul;
         end else if (add) begin
            // add only
            p_core  = p_add;
            NX_core = NX_add;
         end

         sign_core = p_core[15];
         exp_core  = p_core[14:10];
         frac_core = p_core[9:0];

         INV_finite = 1'b0;      // invalid already handled in special path
         NX_finite  = NX_core;
         OF_finite  = 1'b0;
         UF_finite  = 1'b0;
         p_finite   = p_core;

         // Overflow / underflow only make sense if we actually did an operation
         if (mul || add) begin
            // Overflow: exponent beyond max finite (0x1E)
            if (exp_core > 5'h1E) begin
               OF_finite = 1'b1;
               NX_finite = 1'b1;          // overflow implies inexact
               p_finite  = {sign_core, 5'h1F, 10'd0}; // ±Inf
            end
            // Underflow: subnormal result, treat as signed zero
            else if (exp_core == 5'd0 && frac_core != 10'd0) begin
               UF_finite = NX_core;       // underflow only if any bits were lost
               p_finite  = {sign_core, 5'd0, 10'd0};
            end
         end

         p          = p_finite;
         flags_next = {INV_finite, OF_finite, UF_finite, NX_finite};
      end

      result = p;
      flags  = flags_next;
   end

endmodule

