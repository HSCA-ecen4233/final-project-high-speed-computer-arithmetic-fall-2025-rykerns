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
logic [15:0] p;

always_comb begin
	if (mul) begin
		p={Ps,Re,Rf};
	end else begin
		p=x;
	end
	result=p;
end

//first milestone all flags 0
assign flags = 4'b0000;


   // stubbed ideas for instantiation ideas
   
   // fmaexpadd expadd(.Xe, .Ye, .XZero, .YZero, .Pe);
   // fmamult mult(.Xm, .Ym, .Pm);
   // fmasign sign(.OpCtrl, .Xs, .Ys, .Zs, .Ps, .As, .InvA);
   // fmaalign align(.Ze, .Zm, .XZero, .YZero, .ZZero, .Xe, .Ye, .Am, .ASticky, .KillProd);
   // fmaadd add(.Am, .Pm, .Ze, .Pe, .Ps, .KillProd, .ASticky, .AmInv, .PmKilled, .InvA, .Sm, .Se, .Ss);
   // fmalza lza (.A(AmInv), .Pm(PmKilled), .Cin(InvA & (~ASticky | KillProd)), .sub(InvA), .SCnt);

 
endmodule

