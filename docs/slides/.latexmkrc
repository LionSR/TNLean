$pdf_mode = 1;
$out_dir = '../../build';
my $tenkz_root = $ENV{'TENKZ_ROOT'} // '../../.deps/tenkz';
$ENV{'TEXINPUTS'} = "$tenkz_root/tex/tenkz//:" . ($ENV{'TEXINPUTS'} // '');
