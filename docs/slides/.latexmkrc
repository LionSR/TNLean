$pdf_mode = 1;
$out_dir = '../../build';
use Cwd qw(abs_path);
use File::Spec;
my $tenkz_root = $ENV{'TENKZ_ROOT'} // '../../.deps/tenkz';
$tenkz_root = abs_path($tenkz_root) // File::Spec->rel2abs($tenkz_root);
$ENV{'TEXINPUTS'} = "$tenkz_root/tex/tenkz//:" . ($ENV{'TEXINPUTS'} // '');
