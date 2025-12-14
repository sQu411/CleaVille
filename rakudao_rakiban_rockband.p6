unit class CellComplex;

has Spherpoint @.vertices;
has Spherpoint @.centers;
has Array @.edges;
has Array @.faces;

our $gap = False;
our $vertices = False;
our $filling = 5;
our $denseness = 26;
our $radius = pi / 180;
our $perforation = $radius;

method edgemiddles() {
    @!edges.map: { @!vertices[$_[0]].middle(@!vertices[$_[1]]) }
}

method draw(Observer $eye, @image, @z-buffer, @transform, Color $bg, $blur) {
    say "vertices...", $vertices ?? @!vertices.map({ $_.color = .transform(@transform).standardcolor.combined($bg, $blur) }) !! ();
    say "edges..." if $gap && @!edges.map: {
        my $line = @!vertices[$_[0]].geodesic(@!vertices[$_[1]]);
        $line.color = $line.location(0.5).transform(@transform).standardcolor.combined($bg, $blur);
    };
    print "faces";
    for ^@!centers -> $i {
        print "$i.";
        my $color = @!centers[$i].transform(@transform).standardcolor.combined($bg, $blur);
        my @tocenter = @!faces[$i].map: { @!vertices[$_].geodesic(@!centers[$i]) };
        for ^@tocenter -> $j {
            my $k = ($j - 1) % @tocenter;
            for 1/$denseness, * + 1/$denseness ...^ * >= 1/$filling -> $l {
                my $line = @tocenter[$k].location($l).geodesic(@tocenter[$j].location($l));
                $line.color = $color;
                $eye.drawLine(@image, @z-buffer, $line, 1);
                $line = @tocenter[$k].location(1-$l).geodesic(@tocenter[$j].location(1-$l));
                $line.color = $color;
                $eye.drawLine(@image, @z-buffer, $line, 1) unless $empty;
            }
        }
    }
}

unit class HypEdgePos;

has Num $.a = 0;
has Num $.b = 0;
has Num $.c = 1;
has Num $.d = 0;
has Vertex $.vertex;

method assign-product(HypEdgePos $h1, HypEdgePos $h2) {
    self.bless: :a($h1.a*$h2.c - $h1.b*$h2.d + $h1.c*$h2.a + $h1.d*$h2.b),
                :b($h1.a*$h2.d + $h1.b*$h2.c + $h1.c*$h2.b - $h1.d*$h2.a),
                :c($h1.a*$h2.a + $h1.b*$h2.b + $h1.c*$h2.c - $h1.d*$h2.d),
                :d($h1.a*$h2.b - $h1.b*$h2.a + $h1.c*$h2.d + $h1.d*$h2.c)
}

method dehomogenize() {
    my $denom = $!c² + $!d²;
    Point2D.new: :x(($!a*$!c + $!b*$!d)/$denom), :y(($!b*$!c - $!a*$!d)/$denom)
}

method derive(Vertex $v, Num $len, Num $angle?) {
    my $res = $angle ?? self.new.assign-rotation($angle) !! self.new;
    $res.assign-trans-rot($len);
    $res.assign-product(self, $res);
    $res.vertex = $v;
    $res
}

unit class HypEnergy is Energy;

has Logger $.logger = Logger.new: :class(self);

method scale() { }  # Fixed scale

method lamda-to-length(Num $lamda) {
    2 * arsinh(exp($lamda / 2))
}

method length-angle-factor(Num $length) {
    sinh($length / 2)
}

method value-terms() {
    my @terms;
    for @!angles -> $a {
        my $alpha = $a.angle;
        my $lamda = $a.opposite-edge.log-length;
        my $u = $a.vertex.u;
        my $beta = (π + $alpha - $a.next-angle.angle - $a.next-angle.next-angle.angle) / 2;
        @terms.append: -($alpha * $u), $beta * $lamda, Clausen.cl2(2*$alpha)/2, Clausen.cl2(2*$beta)/2;
    }
    # ... triangles, vertices ...
    @terms
}

method hessian($h) {
    $h //= LowerSPDPackMatrix.new: self.input-dimension;
    $h.zero;
    for @!angles -> $a {
        next unless 0 < $a.angle < π;
        my $alpha = $a.angle;
        my $beta = (π + $alpha - $a.next-angle.angle - $a.next-angle.next-angle.angle) / 2;
        my $l = $a.opposite-edge.length;
        my $cot = cos($beta) / sin($beta);
        my $cot2 = $cot / 2;
        my $tanh = tanh($l / 2);
        my $tanhSq = $tanh²;
        my $diag = $cot2 * ($tanhSq + 1);
        my $nonDiag = $cot2 * ($tanhSq - 1);
        my $i = $a.next-vertex.index;
        my $j = $a.prev-vertex.index;
        $h.add($i, $i, $diag) if $i ≥ 0;
        if $j ≥ 0 {
            $h.add($j, $j, $diag);
            $h.add($i, $j, $nonDiag) if $i ≥ 0;
            $h.add($j, $i, $nonDiag) if $i ≥ 0;
        }
    }
    $h
}

sub arsinh(Num $x) {
    log($x + sqrt($x² + 1))
}

unit class Schlaefli;

method sin-cos-half-dihedral(@schlafli) {
    my $ss = 0;
    for @schlafli -> $q {
        $ss = (cos(π/$q)²) / (1 - $ss);
    }
    $ss = 1 if abs(1 - $ss) < 1e-9;
    (sqrt($ss), sqrt(1 - $ss))
}

method householder-reflection(@v) {
    my $dim = @v.elems;
    my @identity = [0..$dim-1].map: -> $i { [0..$dim-1].map: -> $j { $i == $j ?? 1 !! 0 } };
    my @outer = @v.map: -> $x { @v.map: -> $y { $x * $y } };
    @identity.map: -> @row { @row Z- @outer[0].map: * * 2 }
}

method make-regular-polytope(@schlafli) {
    my $dim = @schlafli.elems + 1;
    return [[0e0, 1e0], []] if $dim == 1;
    my @facet = self.make-regular-polytope(@schlafli[0..*-2]);
    my @verts = @facet[0].map: * ~ [0e0];
    # ... symmetry expansion ...
    (@verts, @facet[1])
}

unit class HypLayout is Layout;

has Logger $.logger = Logger.new: :class(self);

method layout-start(Triangle $t) {
    my $a = $t.angles[0];
    my ($v1, $v2) = $a.vertex, $a.next-vertex;
    my $e12 = $a.next-edge;
    my $l12 = $e12.length;

    my $pos1 = HypEdgePos.new: :$v1;
    $v1.offer-location(0, 0);
    $e12.offer-hyp-pos($pos1);
    my $p2 = $pos1.derive($v2, $l12).dehomogenize;
    $v2.offer-location($p2.x, $p2.y);
    self.layout-edge($e12, $t);
}

method layout-edge(Edge $e, Triangle $t) {
    my $c = $t.opposite-vertex($e);
    my ($bac, $cba) = $t.next-angle($c), $t.prev-angle($c);
    my ($a, $b) = $bac.vertex, $cba.vertex;
    my ($ca, $bc) = $bac.prev-edge, $cba.next-edge;
    my ($alpha, $beta) = $bac.angle, $cba.angle;

    my $ab-pos = $e.hyp-pos;
    my $ca-pos = $ca.offer-hyp-pos: $ab-pos.derive($a, $e.length, $alpha);
    my $bc-pos = $bc.offer-hyp-pos: $ab-pos.derive($b, $e.length, -$beta);

    my $caC = $ca-pos.derive($c, $ca.length).dehomogenize;
    my $bcC = $bc-pos.derive($c, $bc.length).dehomogenize;
    my ($x, $y) = ($caC.x + $bcC.x)/2, ($caC.y + $bcC.y)/2;

    die "NaN!" if $x.isNaN || $y.isNaN;
    $c.offer-location($x, $y);
}

unit class Hypersphere;

has Num $.phi;   # [-π, π]
has Num $.psi;   # [-π/2, π/2]
has Num $.theta; # [-π/2, π/2]
has Color $.color = black;

method to-euclid() {
    my ($cφ, $sφ) = cos($!phi), sin($!phi);
    my ($cψ, $sψ) = cos($!psi), sin($!psi);
    my ($cθ, $sθ) = cos($!theta), sin($!theta);
    Euclid.new: :x($cθ*$cψ*$cφ), :y($cθ*$cψ*$sφ), :z($cθ*$sψ), :w($sθ)
}

method distance(Hypersphere $other) {
    my $dot = self.w * $other.w + self.z * $other.z + self.y * $other.y + self.x * $other.x;
    acos($dot.clamp(-1, 1))
}

unit class Spherpoint;

constant $exactness = 0.0005;
constant $black = Color.new(0, 0, 0);

has Num $.phi = 0.0;    # [-π, π]
has Num $.psi = 0.0;    # [-π/2, π/2]
has Num $.theta = 0.0;  # [-π/2, π/2]
has Color $.color = $black;

# Special points
my $northpole = Spherpoint.new(:phi(0), :psi(0), :theta(π/2));
my $southpole = Spherpoint.new(:phi(0), :psi(0), :theta(-π/2));

# Constructors
multi method new() { self.new(:phi(0), :psi(0), :theta(0)) }
multi method new(:$phi!, :$psi!, :$theta!, :$color = $black) {
    self.bless(:$phi, :$psi, :$theta, :$color)
}

# Normalize φ to [-π, π]
method set-phi(Num $new-phi) {
    $!phi = (my $x = $new-phi) % (2*π);
    $!phi -= 2*π if $!phi > π;
    $!phi
}

# Distance in S³
method distance(Spherpoint $other) {
    return 0 if self ≅ $other;
    my $sinθ = sin($!theta) * sin($other.theta);
    my $cosθ = cos($!theta) * cos($other.theta);
    my $sinψ = sin($!psi) * sin($other.psi);
    my $cosψ = cos($!psi) * cos($other.psi);
    my $sinφ = sin($!phi) * sin($other.phi);
    my $cosφ = cos($!phi) * cos($other.phi);
    acos($sinθ + $cosθ * ($sinψ + $cosψ * ($sinφ + $cosφ)))
}

# Geodesic to another point
method geodesic(Spherpoint $dest) {
    my $e1 = self.to-euclid;
    my $e2 = $dest.to-euclid;
    my $momentum = $e1.norm-comp($e2);
    $momentum ×= self.distance($dest) / $momentum.norm;
    Spherline.new(:start(self), :momentum($momentum))
}

# Equality with tolerance
method ACCEPTS(Spherpoint $other) {
    abs($!theta - $other.theta) < $exactness &&
    abs($!psi - $other.psi) < $exactness &&
    abs($!phi - $other.phi) < $exactness
}

# Transform via 4x4 matrix
method transform(@matrix where *.elems == 4) {
    my $e = self.to-euclid.transform(@matrix);
    Spherpoint.new(:phi($e.x), :psi($e.y), :theta($e.z), :color($!color))
}

unit class CellComplex;

has Spherpoint @.vertices;
has Spherpoint @.centers;
has Array @.edges;
has Array @.faces;

our $gap = False;
our $vertices = False;
our $filling = 5;
our $denseness = 26;
our $radius = pi / 180;
our $perforation = $radius;

method edgemiddles() {
    @!edges.map: { @!vertices[$_[0]].middle(@!vertices[$_[1]]) }
}

method draw(Observer $eye, @image, @z-buffer, @transform, Color $bg, $blur) {
    say "vertices...", $vertices ?? @!vertices.map({ $_.color = .transform(@transform).standardcolor.combined($bg, $blur) }) !! ();
    say "edges..." if $gap && @!edges.map: {
        my $line = @!vertices[$_[0]].geodesic(@!vertices[$_[1]]);
        $line.color = $line.location(0.5).transform(@transform).standardcolor.combined($bg, $blur);
    };
    print "faces";
    for ^@!centers -> $i {
        print "$i.";
        my $color = @!centers[$i].transform(@transform).standardcolor.combined($bg, $blur);
        my @tocenter = @!faces[$i].map: { @!vertices[$_].geodesic(@!centers[$i]) };
        for ^@tocenter -> $j {
            my $k = ($j - 1) % @tocenter;
            for 1/$denseness, * + 1/$denseness ...^ * >= 1/$filling -> $l {
                my $line = @tocenter[$k].location($l).geodesic(@tocenter[$j].location($l));
                $line.color = $color;
                $eye.drawLine(@image, @z-buffer, $line, 1);
                $line = @tocenter[$k].location(1-$l).geodesic(@tocenter[$j].location(1-$l));
                $line.color = $color;
                $eye.drawLine(@image, @z-buffer, $line, 1) unless $empty;
            }
        }
    }
}

use NativeCall;

sub ps1-to-obj(Str $rom-path, Str $obj-path) {
    my $rom = $rom-path.IO.open(:bin);
    $rom.seek(2048, SeekFromBeginning);
    my Buf $data = $rom.read($rom.IO.s - 2048);
    $rom.close;

    my @verts;
    my @faces;
    my $i = 0;
    while $i < $data.elems - 8 {
        my $x = nativecast(int16, $data.subbuf($i, 2).reverse) / 1000e0;
        my $y = nativecast(int16, $data.subbuf($i+2, 2).reverse) / 1000e0;
        my $z = nativecast(int16, $data.subbuf($i+4, 2).reverse) / 1000e0;
        @verts.push: ($x, $y, $z);
        $i += 8;

        if $i + 12 <= $data.elems {
            my $a = @verts.end;
            my $b = @verts.end + 1;
            my $c = @verts.end + 2;
            @faces.push: ($a, $b, $c);
            $i += 12;
        }
    }

    my $obj = $obj-path.IO.open(:w);
    for @verts -> $v {
        $obj.say("v {$v[0]} {$v[1]} {$v[2]}");
    }
    for @faces -> $f {
        $obj.say("f {$f[0]+1} {$f[1]+1} {$f[2]+1}");
    }
    $obj.close;
}
