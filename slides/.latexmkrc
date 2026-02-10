$pdf_mode = 1;
$out_dir = '../build';
$biber = 'internal mybiber %O %S';

sub mybiber {
    # Patch bcf version from 3.11 to 3.10 to work with biber 2.19
    my $bcf = $_[-1];
    $bcf =~ s/\.bcf$//;
    my $bcffile = "$bcf.bcf";
    if (-f $bcffile) {
        open(my $fh, '<', $bcffile) or return system("biber", @_);
        my $content = do { local $/; <$fh> };
        close($fh);
        $content =~ s/version="3\.11"/version="3.10"/g;
        open($fh, '>', $bcffile) or return system("biber", @_);
        print $fh $content;
        close($fh);
    }
    return system("biber", @_);
}
