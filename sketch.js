 //mode
var from_front = 1;
var has_gut = 0;
var output_flag = 1;
var extrudable_flag = 1;

var k_spring = 0;
var c_spring = 0;

var particle = [],
  leg_tip = [],
  rts = [],
  sp = [],
  ts = [];
var numMass = 3,
  dt = 0.01,
  Mass = 0.3,
  radius = 15;
var numJoint = numMass - 1;
var numSp    = numMass - 1;
var numRTM = 0;//countします

var L_rts = radius * 1.5,
  k_rts = 50,//do not change. 2017/09/18 "50"
  c_rts = 3.0,
  omg = 2 * Math.PI,
  amp = 0.5;
var k_ts = 1000.0;
var angle_n = Math.PI;
var k_leg = 100.0;
var c_leg = 2;
var time_step = 0;
var data_output_freq = 10,
  MAX_TIME_STEP = 1000;
var drc = new p5.Vector(0, -1); //createVectorはグローバル変数では使えない
var gravity = new p5.Vector(0, 0); //createVectorはグローバル変数では使えない
var time_list = [];
var protest_p = 0; //後ろから何番目か？
var data_table;

// okuya
var locomotion_speed = new p5.Vector(0,0);
var CoM_r = new p5.Vector(0,0);//Centor_of_mass, r means 位置
var CoM_r_0 = new p5.Vector(0,0);//start
var CoM_r_End = new p5.Vector(0,0);//MAX_TIME_STEP
var direction_End = 0;

var PI_coef_1 = 0;
var PI_coef_1_counter = 0;
//var PI_coef_1_array = [1.3];
var PI_coef_1_array = [1.5,1.4,1.3,1.2,1.1,1.0,0.9,0.8, 0.7, 0.6,0.5, 0.4];

var PI_coef_re_center = 0;
var PI_coef_re_center_counter = 0;
var PI_coef_re_center_array = [0, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 1.75];

var PI_coef_re_width = 0.25;
var PI_coef_re_width_counter = 0;
var PI_coef_re_width_array = [0.25];//

var Consume_Energy = 0;

var Output_Table_speed_x = new Array ();
var Output_Table_speed_y = new Array ();
var Output_Table_dir = new Array ();
var Output_Table_energy = new Array();
var Output_Table_trajectory = new Array();


function round3disp(number) {
  return Math.round(number * 1000)/1000;
}
//-----------------------------------------------------------------------
//                            O B J E C T S
//-----------------------------------------------------------------------
function get_naiseki(_r1, _r2) {
  return _r1.x * _r2.x + _r1.y * _r2.y;
}
function get_angle(_r1, _r2) {
  var gaiseki = _r1.x * _r2.y - _r1.y * _r2.x;
  var naiseki = _r1.x * _r2.x + _r1.y * _r2.y;
  return (atan2(gaiseki, naiseki));
}
function get_direction_deg() {
  return atan2(particle[numMass-1].r.y - particle[0].r.y, particle[numMass-1].r.x - particle[0].r.x)* 360 / (2*Math.PI);
}

function Particle(x, y, r) {
  this.r = createVector(x, y);
  this.pr = createVector(x, y); //位置ベクトルr?
  this.v = createVector(0, 0);
  this.pv = createVector(0, 0);
  this.f = createVector(0, 0);
  this.pf = createVector(0, 0);
  this.theta = 0;
  this.ptheta = 0;
  this.radius = r;
  this.mass = 0;

  this.save_prev = function() {
    this.pr = this.r;
    this.pv = this.v;
    this.pf = this.f;
  }
  this.add_f = function(_f) {
    this.f.x += _f.x;
    this.f.y += _f.y;
  }
  this.sub_f = function(_f) {
    this.f.x -= _f.x;
    this.f.y -= _f.y;
  }
  this.reset_f = function() {
    this.f.x = 0;
    this.f.y = 0;
  }

  //x(t+dt) = x(t) + v dt + 1/2 a (dt)^2
  this.update_r = function() {
    this.r.x = this.pr.x + this.pv.x * dt + 0.5 * this.pf.x / this.mass * dt * dt; //this.r.x = this.pr.x + dt * ( this.pv.x + 0.5*dt*dt/Mass*this.pf.x);
    this.r.y = this.pr.y + this.pv.y * dt + 0.5 * this.pf.y / this.mass * dt * dt; //同様
  }
  //v(t+dt) = v(t) + 1/2 a dt. 但し、a is (a[t]+a[t+dt])/2。なぜここはpfだけじゃないんだ？
  this.update_v = function() {
    this.v.x = this.pv.x + 0.5 * (this.f.x + this.pf.x) / this.mass * dt;
    this.v.y = this.pv.y + 0.5 * (this.f.y + this.pf.y) / this.mass * dt;
  }
  this.set_r = function(vec) {
    this.r = vec.copy();
  }

  this.set_theta = function(val) {    this.theta = val;  }
  this.save_ptheta = function() {
    this.ptheta = this.theta;
  }
  this.update_theta = function() {
    //theta は体節固有の値
    this.theta = this.ptheta + omg * dt;
    while (this.theta > 2 * Math.PI) {
      this.theta -= 2 * Math.PI;
    }
  }
  this.show = function() {
    stroke(46, 139, 87); //イモムシの輪郭の色
    strokeWeight(2); //イモムシの輪郭の太さ
    fill(0, 255, 154, 125); //イモムシの体節の色（RGBA(透明度)）
    ellipse(this.r.x, this.r.y, 2 * this.radius, 2 * this.radius);
  }
}

//Realtime Tunable Spring
function RTM(p_i, p_j, Length) {
  this.from = p_i;
  this.to = p_j; //始点と終点
  this.theta = 0;
  this.ptheta = 0;
  this.dif = createVector(this.to.r.x - this.from.r.x, this.to.r.y - this.from.r.y);
  this.l = mag(this.dif.x, this.dif.y); //mag means magnitude.　this is the length of spring.
  this.L_rts = Length; //this.L_rtsは変化する自然長、L_rtsは初期値
  this.L_rts_max = Length; //変化しない自然長
  this.amp = amp; //
  this.k = k_rts; //spring constant
  this.c = c_rts; //damper constant()
  this.force = createVector(0, 0);
  this.tension = 0.0;

  this.save_ptheta = function() {
    this.ptheta = this.theta;
  }
  this.update_theta = function() {
    //theta は体節固有の値
    this.theta = this.ptheta + omg * dt;
    while (this.theta > 2 * Math.PI) {
      this.theta -= 2 * Math.PI;
    }
  }
  //update Length of spring?
  this.update_L = function() {
    this.L_rts = this.L_rts_max * (1 + this.amp * cos(this.theta));
  }
  //calculation force
  this.calc_f = function() {
    this.dif.x = this.to.r.x - this.from.r.x;
    this.dif.y = this.to.r.y - this.from.r.y;
    this.l = mag(this.dif.x, this.dif.y);
    //バネの長さが0じゃない
    if (this.l != 0) {
      var e_dif = createVector(this.dif.x / this.l, this.dif.y / this.l); //error　xyそれぞれの要素の割合
      var targ = createVector(this.from.r.x + this.L_rts * e_dif.x, this.from.r.y + this.L_rts * e_dif.y); //もしバネが自然長なら、バネの端がどこにあるか
      stroke(0);//足black
      fill(0, 150);//足の付根, Gray,透明度
      //ellipse(targ.x, targ.y, 0.5 * radius, 0.5 * radius);//足の付根近くに実は円がある。色が変わる。
      //目標値までの距離？ distance
      var dis = createVector(targ.x - this.to.r.x, targ.y - this.to.r.y);
      // F=-kx,より F = x*(-k)
      if(this.L_rts < this.l){
        this.force = dis.mult(-this.k);
      }else{
        if(extrudable_flag == 1){
          this.force = dis.mult(-this.k);
        } else {
          this.force.set(0, 0);
        }
      }
    } else {
      this.force.set(0, 0);
    }
    //fromに対するtoの相対速度
    var relative_v = createVector(this.to.v.x - this.from.v.x, this.to.v.y - this.from.v.y);
    this.force.add(this.c * relative_v.x, this.c * relative_v.y); //ダンパによる力
    this.tension = this.k * (this.L_rts - this.l); // 張力はkx.バネが縮もうとする力
  }

  this.set_theta = function(val) {    this.theta = val;  }
  this.set_k     = function(val) {    this.k = val;  }
  this.set_c     = function(_c)  {    this.c = _c;  }
  this.set_L     = function(val) {    this.L_rts = val;  }
  this.set_L_max = function(val) {    this.L_rts_max = val;  }
  this.set_amp  = function(_amp) {    this.amp = _amp;  }
  this.show = function() {
    stroke(0);
    fill(0, 255);
    //
    if (this.L_rts_max > 0) {
      line(this.from.r.x, this.from.r.y, this.to.r.x, this.to.r.y);
    } else if (this.L_rts_max == 0) {
    }
  }
}
function Spring(p_i, p_j, Length) {
  this.from = p_i;
  this.to = p_j; //始点と終点
  this.theta = 0;
  this.ptheta = 0;
  this.dif = createVector(this.to.r.x - this.from.r.x, this.to.r.y - this.from.r.y);
  this.l = mag(this.dif.x, this.dif.y); //mag means magnitude.　this is the length of spring.
  this.L_rts = Length; //this.L_rtsは変化する自然長、L_rtsは初期値
  this.L_rts_max = Length; //変化しない自然長
  this.amp = amp; //
  this.k = k_spring; //spring constant
  this.c = c_spring; //damper constant()
  this.force = createVector(0, 0);
  this.tension = 0.0;

  this.save_ptheta = function() {
    this.ptheta = this.theta;
  }
  this.update_theta = function() {
    //theta は体節固有の値
    this.theta = this.ptheta + omg * dt;
    while (this.theta > 2 * Math.PI) {
      this.theta -= 2 * Math.PI;
    }
  }
  //update Length of spring?
  this.update_L = function() {
    this.L_rts = this.L_rts_max * (1 + this.amp * cos(this.theta));
  }
  //calculation force
  this.calc_f = function() {
    this.dif.x = this.to.r.x - this.from.r.x;
    this.dif.y = this.to.r.y - this.from.r.y;
    this.l = mag(this.dif.x, this.dif.y);
    //バネの長さが0じゃない
    if (this.l != 0) {
      var e_dif = createVector(this.dif.x / this.l, this.dif.y / this.l); //error　xyそれぞれの要素の割合
      var targ = createVector(this.from.r.x + this.L_rts * e_dif.x, this.from.r.y + this.L_rts * e_dif.y); //もしバネが自然長なら、バネの端がどこにあるか
      stroke(0);//足black
      fill(0, 150);//足の付根, Gray,透明度
      //ellipse(targ.x, targ.y, 0.5 * radius, 0.5 * radius);//足の付根近くに実は円がある。色が変わる。
      //目標値までの距離？ distance
      var dis = createVector(targ.x - this.to.r.x, targ.y - this.to.r.y);
      // F=-kx,より F = x*(-k)
      this.force = dis.mult(-this.k);
    } else {
      this.force.set(0, 0);
    }
    //fromに対するtoの相対速度
    var relative_v = createVector(this.to.v.x - this.from.v.x, this.to.v.y - this.from.v.y);
    this.force.add(this.c * relative_v.x, this.c * relative_v.y); //ダンパによる力
    this.tension = this.k * (this.L_rts - this.l); // 張力はkx.バネが縮もうとする力
  }

  this.set_theta = function(val) {    this.theta = val;  }
  this.set_k     = function(val) {    this.k = val;  }
  this.set_c     = function(_c)  {    this.c = _c;  }
  this.set_L     = function(val) {    this.L_rts = val;  }
  this.set_L_max = function(val) {    this.L_rts_max = val;  }
  this.set_amp  = function(_amp) {    this.amp = _amp;  }
  this.show = function() {
    stroke(0);
    fill(0, 255);
    //
    if (this.L_rts_max > 0) {
      line(this.from.r.x, this.from.r.y, this.to.r.x, this.to.r.y);
    } else if (this.L_rts_max == 0) {
    }
  }
}
//-----------------------------------------------------------------------
//                      S E T U P   &   D R A W
//-----------------------------------------------------------------------
function setup() {
  frameRate(100);
  for ( var i = 0; i < PI_coef_1_array.length +3/*ラベル+備考用*/ ; i++) {
    Output_Table_speed_x[i] = new Array();
    Output_Table_speed_y[i] = new Array();
    Output_Table_dir[i]     = new Array();
    Output_Table_energy[i]  = new Array();
  }
  Output_Table_speed_x[0][0] = "Speed_x";
  Output_Table_speed_y[0][0] = "Speed_y";
  Output_Table_speed_y[PI_coef_1_array.length+1][0] = "k_rts";
  Output_Table_speed_y[PI_coef_1_array.length+2][0] = k_rts;
  Output_Table_speed_y[PI_coef_1_array.length+1][1] = "c_rts";
  Output_Table_speed_y[PI_coef_1_array.length+2][1] = c_rts;
  Output_Table_speed_y[PI_coef_1_array.length+1][2] = "amp";
  Output_Table_speed_y[PI_coef_1_array.length+2][2] = amp;
  Output_Table_speed_y[PI_coef_1_array.length+1][3] = "k_spring";
  Output_Table_speed_y[PI_coef_1_array.length+2][3] = k_spring;
  Output_Table_speed_y[PI_coef_1_array.length+1][4] = "c_spring";
  Output_Table_speed_y[PI_coef_1_array.length+2][4] = c_spring;
  Output_Table_dir[0][0]     = "Direction";
  Output_Table_energy[0][0]  = "Energy";

  for ( var i = 0; i < PI_coef_1_array.length; i++) {
    Output_Table_speed_x[i+1][0] = PI_coef_1_array[i];
    Output_Table_speed_y[i+1][0] = PI_coef_1_array[i];
    Output_Table_dir[i+1][0]     = PI_coef_1_array[i];
    Output_Table_energy[i+1][0]  = PI_coef_1_array[i];
  }
  for( var i = 0; i < PI_coef_re_center_array.length; i++) {
    Output_Table_speed_x[0][i+1] = PI_coef_re_center_array[i];
    Output_Table_speed_y[0][i+1] = PI_coef_re_center_array[i];
    Output_Table_dir[0][i+1]     = PI_coef_re_center_array[i];
    Output_Table_energy[0][i+1]  = PI_coef_re_center_array[i];
  }

    PI_coef_1 = PI_coef_1_array[PI_coef_1_counter];
    PI_coef_re_center = PI_coef_re_center_array[PI_coef_re_center_counter];
    createCanvas(window.innerWidth, window.innerHeight); //createCanvas(200, 200);
    my_setup();
}

function my_setup() {
  numRTM = 0;
  Consume_Energy = 0;
  if(from_front == 1){
    //PI_coef_re = -0.211 * PI_coef_1 + 0.5008;
  }else{
    //PI_coef_re = 0.2882 * PI_coef_1 - 0.4959;
  }
  for (var i = 0; i < numMass; i++) {
    particle[i] = new Particle(window.innerWidth * 0.5, window.innerHeight * 0.5 + L_rts * i, radius);// 体節(mass)
    particle[i].mass = Mass;
    if(from_front)  {
      particle[i].set_theta(-1*(i-0.5)* (PI_coef_1* 2 * Math.PI) / numMass);//前からの波
    }else{
      particle[i].set_theta( 1*(i-0.5)* (PI_coef_1* 2 * Math.PI) / numMass);//後ろからの波　変更点1)
    }
    leg_tip[i]  = new Particle(window.innerWidth * 0.5, window.innerHeight * 0.5 + L_rts * i, 0.2 * radius);// 足
  }

  //realtime tunable spring
  for (var i = 0; i < numJoint; i++) {
    //体節の間のRealtime Tunable Springの設定
    rts[i] = new RTM(particle[i], particle[i + 1], L_rts);
    if(from_front) {
      rts[i].set_theta(-1*i * (PI_coef_1*2*Math.PI) / numMass);//前からの波
    }else{
      rts[i].set_theta( 1*i * (PI_coef_1*2*Math.PI) / numMass);//後ろからの波　変更点1
    }
    rts[i].amp = amp;
    numRTM += 1;
  }

  if ( has_gut ) {  //頭とお尻の間のRealtime Tunable Springの設定
    gut = new Spring(particle[0], particle[numMass-1], L_rts*(numMass-1));
    //rts[numRTM].set_theta(PI_coef_re * Math.PI);//変更点2
    gut.k = k_spring;
    gut.c = c_spring;
    gut.amp = 0;
  }

  //sp is spring? 体節と足の間？
  for (var i = 0; i < numMass; i++) {
    sp[i] = new RTM(particle[i], leg_tip[i], L_rts);
    sp[i].set_L_max(0);
    sp[i].set_L(0);
    sp[i].set_amp(0);
  }

  //output
  table = new p5.Table();
  table.addColumn('id');
  table.addColumn('t_step');
  table.addColumn('tension');
  var newRow = table.addRow();
  newRow.setNum('id', table.getRowCount() - 1);
  newRow.setString('t_step', time_step);
  newRow.setString('tension', rts[0].tension);
}

function draw() {
  if(time_step == 0) {//start
    my_setup();
  }
  if(time_step == MAX_TIME_STEP+10) {
    //データの保存
    Output_Table_speed_x[PI_coef_1_counter + 1][PI_coef_re_center_counter + 1] = 1000*locomotion_speed.x;
    Output_Table_speed_y[PI_coef_1_counter + 1][PI_coef_re_center_counter + 1] = 1000*locomotion_speed.y;
    Output_Table_dir[PI_coef_1_counter + 1][PI_coef_re_center_counter + 1]     = direction_End;
    Output_Table_energy[PI_coef_1_counter + 1][PI_coef_re_center_counter + 1]  = Consume_Energy;

    time_step = 0;
    if ( PI_coef_1_counter < PI_coef_1_array.length - 1) {
      PI_coef_1_counter++;
    }else{
      PI_coef_1_counter = 0;
      if ( PI_coef_re_center_counter < PI_coef_re_center_array.length - 1) {
        PI_coef_re_center_counter++;
      }else{//simulation is finished.
        if( output_flag ) {
          //save(Output_Table_speed_x, 'Speed_x');//小数点があるときはsaveStrings
          save(Output_Table_speed_y, 'Speed_y');//小数点があるときはsaveStrings
          //save(Output_Table_dir, 'Dir');//小数点があるときはsaveStrings
          //save(Output_Table_energy, 'Energy');//小数点があるときはsaveStrings
          //save(Output_Table_trajectory, 'trajectory');//小数点があるときはsaveStrings
        }
        time_step =10 * MAX_TIME_STEP;//Frag
      }
    }
    PI_coef_1 = PI_coef_1_array[PI_coef_1_counter];
    PI_coef_re_center = PI_coef_re_center_array[PI_coef_re_center_counter];
    my_setup();
  }

  background(200); //背景色の明るさ=200
  for (var i = 0; i < numMass; i++) {    particle[i].save_prev();  }
  for (var i = 0; i < numRTM ; i++) {    rts[i].save_ptheta();  }
  for (var i = 0; i < numMass; i++) {    particle[i].save_ptheta();  }
  for (var i = 0; i < numRTM ; i++) {    rts[i].update_theta();  }
  for (var i = 0; i < numMass; i++) {    particle[i].update_theta();  }
  for (var i = 0; i < numRTM ; i++) {    rts[i].update_L();  }
  for (var i = 0; i < numMass; i++) {    particle[i].reset_f();  }
  for (var i = 0; i < numRTM ; i++) {//バネによる力を計算しrts.forceをF=-kxを用いて計算。
    rts[i].calc_f();
    rts[i].from.add_f(rts[i].force);//体節iに力を与え、その反作用を体節i+1に与える
    rts[i].to.add_f(rts[i].force.mult(-1));
  }
  for (var i = 0; i < numRTM ; i++) {//ここでRTMのエネルギーを計算
    if ( get_naiseki(rts[i].force, rts[i].from.v) < 0)
    Consume_Energy -= get_naiseki(rts[i].force, rts[i].from.v)*dt;
  }
  if( has_gut ) {
    gut.save_ptheta();
    gut.update_theta();
    gut.update_L();
    gut.calc_f();//腸の力
    gut.from.add_f(gut.force);
    gut.to.add_f(gut.force.mult(-1));
    //腸のエネルギー
    if ( get_naiseki(gut.force, gut.from.v) < 0)
    Consume_Energy -= get_naiseki(gut.force, gut.from.v)*dt;
  }

  /// この部分で脚の把持・開放を制御している------------------------------------
  //後ろprotest_p本以外の制御
  var eval = [];//配列
  for (var i = 0; i < numMass; i++) {eval[i] = drc.x * particle[i].v.x + drc.y * particle[i].v.y;}//drcもRTMの数だけ必要。

  for (var i = 0; i < numMass; i++) {//放したいのは前に進むとき。前に進むのはcosの差が大きいとき。つまり加法定理よりsinが小きくなるとき。よってΘが3/2π。でもバネで位相が遅れるかもしれない...?
    var leg_release_center = PI_coef_re_center * Math.PI;// + atan(c_rts * omg/(k_rts- Mass * omg * omg));
    text(round3disp(leg_release_center), 100, 400);//
    var leg_release_width  = PI_coef_re_width * 2 * Math.PI;// / numMass;
//0のとき危ない。
    var leg_release_start = leg_release_center - leg_release_width/2;
    var leg_release_end   = leg_release_center + leg_release_width/2;
    while ( leg_release_start < 0 ) { leg_release_start += 2 * Math.PI; }
    while ( leg_release_end   < 0 ) { leg_release_end += 2 * Math.PI; }

    while ( 2*Math.PI < leg_release_start ) { leg_release_start -= 2 * Math.PI; }
    while ( 2*Math.PI < leg_release_end   ) { leg_release_end   -= 2 * Math.PI; }
    text(round3disp(leg_release_start), 100, 420);//
    text(round3disp(leg_release_end), 100, 440);//
    var leg_release_start_is_faster_than_end;
    if (leg_release_start < leg_release_end) { leg_release_start_is_faster_than_end = 1; } else { leg_release_start_is_faster_than_end = 0; }
    if (
      leg_release_width == 0 ||
      (
        (
         leg_release_start_is_faster_than_end==1 && ( particle[i].theta < leg_release_start || leg_release_end   < particle[i].theta)
        )
         ||
        (
         leg_release_start_is_faster_than_end==0 && ( leg_release_end  < particle[i].theta  && particle[i].theta < leg_release_start)
        )
      )
    )
    {//接地条件
      sp[i].set_k(k_leg);
      sp[i].set_c(c_leg);
      strokeWeight(1);
    } else {//足を浮かせる
      sp[i].set_k(0); // sp is one of RTM. if k is 0, F = 0 because -kx = 0.
      sp[i].set_c(0);
      leg_tip[i].set_r(particle[i].r);//足を体節に追従
      strokeWeight(0);
    }
    text(concat("v_",i), 10,40+20*i);
    text(round3disp(eval[i]), 100, 40+20*i);//
  }
  //体節と足の間の力を計算し、体節に掛かる力を加算。
  for (var i = 0; i < numMass; i++) {
    sp[i].calc_f();
    sp[i].from.add_f(sp[i].force);
  }
  for (var i = 0; i < numMass; i++) {particle[i].add_f(gravity);  }//重力
  for (var i = 0; i < numMass; i++) {particle[i].update_r();}
  for (var i = 0; i < numMass; i++) {particle[i].update_v();}
  for (var i = 0; i < numMass; i++) {particle[i].show();}
  for (var i = 0; i < numMass; i++) {leg_tip[i].show();
  }//なぜ4つあるのだろう?
  for (var i = 0; i < numRTM ; i++) {rts[i].show();}
  for (var i = 0; i < numSp  ; i++) {sp[i].show();
  }

  //髭の描写
  var hige = createVector(rts[0].to.r.x - rts[0].from.r.x, rts[0].to.r.y - rts[0].from.r.y);
  strokeWeight(2);
  hige.normalize();
  hige.rotate(5 * PI / 6);
  line(particle[0].r.x + radius * hige.x, particle[0].r.y + radius * hige.y, particle[0].r.x + 1.6 * radius * hige.x, particle[0].r.y + 1.6 * radius * hige.y);
  hige.rotate(2 * PI / 6);
  line(particle[0].r.x + radius * hige.x, particle[0].r.y + radius * hige.y, particle[0].r.x + 1.6 * radius * hige.x, particle[0].r.y + 1.6 * radius * hige.y);
  //text("p0: ", 10, 40); text(particle[0].r, 40, 40);
  //console.log(10);

  //足の描写
  for (var i = 0; i < numMass; i++) { // Drawing leg when it grips
    if (0 < sp[i].k) { // if grips.
      var leg_left = createVector();
      var leg_right = createVector();
      if ( i == 0 ) {
        leg_left.set(rts[i].from.r.x -rts[i].to.r.x, rts[i].from.r.y -rts[i].to.r.y);
      }else if ( i == numMass-1 ) {
        leg_left.set(rts[i-1].from.r.x -rts[i-1].to.r.x, rts[i-1].from.r.y -rts[i-1].to.r.y);
      }else{
        leg_left.set(rts[i].from.r.x -rts[i].to.r.x + rts[i-1].from.r.x -rts[i-1].to.r.x, rts[i].from.r.y -rts[i].to.r.y+rts[i-1].from.r.y -rts[i-1].to.r.y);
      }
//      leg_left.set(particle[i].v);
      leg_left.normalize();
      leg_left.rotate(HALF_PI);
      leg_right = leg_left.copy();
      leg_right.rotate(Math.PI);
      line(particle[i].r.x, particle[i].r.y, particle[i].r.x + 1.5 * radius * leg_left.x, particle[i].r.y + 1.5 * radius * leg_left.y);
      line(particle[i].r.x, particle[i].r.y, particle[i].r.x + 1.5 * radius * leg_right.x, particle[i].r.y + 1.5 * radius * leg_right.y);
    }
  }
  //text(time_list, 100, 100);
  if (time_step % data_output_freq == 0) {
    //time_list.push(str(time_step));
    var newRow = table.addRow();
    newRow.setNum('id', table.getRowCount() - 1);
    newRow.setString('t_step', time_step);
    newRow.setString('tension', rts[0].tension);
  }

  CoM_r.set(0,0);
  for (var i = 0; i < numMass; i++ ) {
    CoM_r.add(particle[i].r.x, particle[i].r.y);
  }
  CoM_r.div(numMass);
  strokeWeight(1)
  text("CoM_r: ", 10, 200);
  text([round3disp(CoM_r.x), round3disp(CoM_r.y)], 100, 200);
  Output_Table_trajectory[time_step] = CoM_r.y;

  if (time_step == 0) {
      CoM_r_0 = CoM_r.copy();
  }
  if (MAX_TIME_STEP <= time_step) {
    if(MAX_TIME_STEP == time_step) {
      CoM_r_End = CoM_r.copy();
    locomotion_speed.x = (CoM_r_End.x - CoM_r_0.x) / MAX_TIME_STEP;
    locomotion_speed.y = -1*(CoM_r_End.y - CoM_r_0.y) / MAX_TIME_STEP;
    direction_End = get_direction_deg();
  }
    strokeWeight(1);
    text("CoM_r_End: ", 10, 220);
    text([round3disp(CoM_r_End.x),round3disp(CoM_r_End.y)], 100, 220);
  }
  strokeWeight(1)
  text("time_step:", 10, 20);
  text(time_step, 100, 20);
  if( has_gut==1)    {text("has gut", 200, 20);  }else{text("no gut", 200, 20);  }
  if( from_front==1) {text("front", 300, 20);    }else{text("back", 300, 20);  }
  text("k_gut: ", 350, 20);
  text(k_spring, 400, 20);


  text("speed: ", 10, 160);
  text([round3disp(1000*locomotion_speed.x),round3disp(1000* locomotion_speed.y)], 100, 160);
  text("PI_coef_1: ", 10, 260);
  text(round3disp(PI_coef_1), 100, 260);
  text("PI_coef_re_wid: ", 10, 280);
  text(round3disp(PI_coef_re_width), 100, 280);
  text("PI_coef_re_cent: ", 10, 300);
  text(round3disp(PI_coef_re_center), 100, 300);
  text("Energy: ", 10, 320);
  text(round3disp(Consume_Energy), 100, 320);

  time_step++;
}
