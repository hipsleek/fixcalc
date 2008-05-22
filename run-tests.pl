#!/usr/bin/perl

use File::Find;
use File::Basename;
use Getopt::Long;

GetOptions( "stop"  => \$stop,
			"exhaustive"  => \$exhaustive,
			"help" => \$help);
if ($help){
	print "run-tests.pl [-stop][-exhaustive] test-suite-list\n";
	exit(0);}
@param_list = @ARGV;
$module_path = '/home/popeeaco/personal/research/bugs-code';
$exempl_path = "$module_path/examples";
$exec_path = "$module_path";
@excl_files = (); # "pepm08/FFT","pepm08/linpack","pepm08/LU","fse08/BAD_SpamAssasin","fse08/BAD_Samba";
#rezultatele pot fi: POSSIBLE|SAFETY|BUG
%runs = (
    "asian06" =>[
            ["pepm08/bsearch","POSSIBLE","+infer +check -o:con1 PostStrong -m:2"],
						["pepm08/bubblesort","SAFETY","+infer +check -o:con1 PostStrong -m:2"],
						["pepm08/copyseq","SAFETY","+infer +check -o:con1 PostStrong -m:2"],
						["pepm08/dotprod","SAFETY","+infer +check -o:con1 PostStrong -m:2"],
						["pepm08/initarr","SAFETY","+infer +check -o:con1 PostStrong -m:2"],
						["pepm08/intro","POSSIBLE","+infer +check -o:con1 PostStrong -m:1"],
						["pepm08/intro2","POSSIBLE","+infer +check -o:con1 PostStrong -m:1"],
						["pepm08/mergesort","SAFETY","+infer +check -o:con1 PostStrong -m:4"],
						["pepm08/mvm","SAFETY","+infer +check +indir -o:con1 PostStrong -m:2"],
						["pepm08/queens","POSSIBLE","+infer +check -o:con1 PostStrong -m:2"],
						["pepm08/quicksort","POSSIBLE","+infer +check -o:con1 PostStrong -m:2"],
						["pepm08/sentinel","POSSIBLE","+infer +check -o:con1 PostStrong -m:1"],
						["pepm08/sumvec","SAFETY","+infer +check -o:con1 PostStrong -m:2"],
						["pepm08/swaparr","SAFETY","+infer +check -o:con1 PostStrong -m:1"],
#						["pepm08/FFT","POSSIBLE","+infer +check -o:con1 PostStrong -m:3"],
#						["pepm08/linpack","POSSIBLE","+infer +check -o:con1 PostStrong -m:2"],
#						["pepm08/LU","POSSIBLE","+infer +check -o:con1 PostStrong -m:2"],
						["pepm08/SOR","SAFETY","+infer +check -o:con1 PostStrong -m:4"]
						],
    "pepm08" =>[
            ["pepm08/bsearch","SAFETY","+infer +check -o:con1 StrongStrong -m:1"],
						["pepm08/bubblesort","SAFETY","+infer +check -o:con1 StrongStrong -m:1"],
						["pepm08/copyseq","SAFETY","+infer +check -o:con1 StrongStrong -m:1"],
						["pepm08/dotprod","SAFETY","+infer +check -o:con1 StrongStrong -m:1"],
						["pepm08/initarr","SAFETY","+infer +check -o:con1 StrongStrong -m:1"],
						["pepm08/intro","POSSIBLE","+infer +check -o:con1 StrongStrong -m:1"],
						["pepm08/intro2","POSSIBLE","+infer +check -o:con1 StrongStrong -m:1"],
						["pepm08/mergesort","SAFETY","+infer +check -o:con1 StrongWeak -m:1"],
						["pepm08/mvm","SAFETY","+infer +check +indir -o:con1 StrongStrong -m:1"],
						["pepm08/queens","SAFETY","+infer +check -o:con1 StrongStrong -m:1"],
						["pepm08/quicksort","SAFETY","+infer +check -o:con1 StrongStrong -m:2"],
						["pepm08/sentinel","POSSIBLE","+infer +check -o:con1 StrongStrong -m:1"],
						["pepm08/sumvec","SAFETY","+infer +check -o:con1 StrongStrong -m:1"],
						["pepm08/swaparr","SAFETY","+infer +check -o:con1 StrongStrong -m:1"],
						["pepm08/FFT","SAFETY","+infer +check -o:con1 StrongStrong -m:1"],
#						["pepm08/linpack","POSSIBLE","+infer +check -o:con1 StrongWeak -m:2"],
						["pepm08/LU","SAFETY","+infer +check -o:con1 StrongStrong -m:1"],
						["pepm08/SOR","SAFETY","+infer +check -o:con1 StrongStrong -m:1"]
						],
#		"fse08" => [
#		        ["fse08/errbsearch","SAFETY","+infer +check -o:con1 PostStrong -m:1"],
#						["fse08/errbubblesort","SAFETY","+infer +check -o:con1 PostStrong -m:1"],
#						["fse08/errinitarr","SAFETY","+infer +check -o:con1 PostStrong -m:1"],
#						["fse08/errmergesort","SAFETY","+infer +check -o:con1 PostStrong -m:1"],
#						["fse08/errqueens","SAFETY","+infer +check -o:con1 PostStrong -m:1"],
#						["fse08/errquicksort","SAFETY","+infer +check -o:con1 PostStrong -m:1"],
#						["fse08/errsentinel","SAFETY","+infer +check -o:con1 PostStrong -m:1"],
#						["fse08/BAD_Samba","SAFETY","+infer +check -o:con1 PostStrong -m:1"],
#						["fse08/BAD_SpamAssasin","SAFETY","+infer +check -o:con1 PostStrong -m:1"]],
		"gulavani-fse06" =>[
		        ["gulavani-fse06/fse.fig1","SAFETYBUG","+infer +check -o:con1 DualStrong -m:1"],
						["gulavani-fse06/fse.fig3","SAFETY","+infer +check -o:con1 DualStrong -m:1"],
						["gulavani-fse06/fse.fig4","BUG","+infer +check -o:con1 DualStrong -m:1"],
						["gulavani-fse06/fse.fig6","SAFETY","+infer +check -o:con1 DualStrong -m:1"],
						["gulavani-fse06/fse.fig7","SAFETYBUG","+infer +check -o:con1 DualStrong -m:1"],
						["gulavani-fse06/fse.fig8","SAFETY","+infer +check -o:con1 DualStrong -m:1"],
						["gulavani-fse06/fse.fig9","BUG","+infer +check -o:con1 DualStrong -m:2"]],
);		

%result = ("SAFETY"=>0,"POSSIBLE"=>0,"BUG"=>0,"UNEXPECTED"=>0); 

$error_count = 0;
$error_files = "";
$output_file = "$module_path/log";
$iter_limit = 2;
$tests = 0;

$time1=`date +"%s"`;
open(LOGFILE, "> $output_file") || die ("Could not open $output_file.\n");
	if ($exhaustive) 
		{
				@done = ();
				foreach $key (keys %runs){
					$t_list = $runs{$key};
					foreach $test (@{$t_list})
					{
						if (not(grep(/^($test->[0])$/,@excl_files))&& not(exists $test->[0], @done)){
						  @done = push(@done,$test->[0]);
							print LOGFILE  "Checking $test->[0]\n";
							for($i=1;$i<=$iter_limit;$i++){
								check_one_file("examples/$test->[0].imp",$i,"DualStrong" );
							}
				        print LOGFILE "\n======================================\n";
						}
					}
				}	
			if ($error_count > 0) {
			  print LOGFILE "Total number of errors: $error_count in files: $error_files.\n";
			}
		}
	else
		{
			foreach $param (@param_list)
			{
				$t_list = $runs{$param};	
				foreach $test (@{$t_list})
				{
					if (not(grep(/^($test->[0])$/,@excl_files))){
					$r = "";
					print "./imp examples/$test->[0].imp $test->[2]\n";
					print LOGFILE "./imp examples/$test->[0].imp $test->[2]\n";
					$output = `cd $exec_path ;./imp examples/$test->[0].imp $test->[2]`;	
					print LOGFILE "$output\n============\n";
					if ($output =~ /[\n]\s*POSSIBLE/)
						{$r = "POSSIBLE";
						  if($test->[1]=~ /POSSIBLE/)
						  {
    						 $result{"POSSIBLE"} = $result{"POSSIBLE"} +1;
    						 $tests++;
						  }
						  
						}
					if($output =~ /[\n]\s*SAFETY/ )
						{$r = $r."SAFETY";
						  if($test->[1]=~ /SAFETY/)
						    {
						      $result{"SAFETY"} = $result{"SAFETY"} +1;
						      $tests++;
						    }
						  }
					if($output =~ /[\n]\s*BUG/ )
						{$r = $r."BUG";
						 if($test->[1]=~ /BUG/)
						 {
						    $result{"BUG"} = $result{"BUG"} +1;
						  	$tests++;   
						 }    
						 }
					print "$r $test->[1]\n";
					print LOGFILE "$r $test->[1]\n";
					if($r!~ /^($test->[1])$/)
					{
						print LOGFILE "unexpected result for $param $test->[0]\n";
						$result{"UNEXPECTED"} = $result{"UNEXPECTED"} +1;
						$tests++;
					}
				  }
				}
			}
		print "------\n Total tests: $tests\n out of which:\n";
		print "\tPOSSIBLE: $result{'POSSIBLE'}\n\tSAFETY: $result{'SAFETY'}\n";
		print "\tBUG: $result{'BUG'}\n \tUNEXPECTED: $result{'UNEXPECTED'}\n";
		print LOGFILE "------\n Total tests: $tests\n out of which:\n";
		print LOGFILE "\tPOSSIBLE: $result{'POSSIBLE'}\n\tSAFETY: $result{'SAFETY'}\n";
		print LOGFILE "\tBUG: $result{'BUG'}\n \tUNEXPECTED: $result{'UNEXPECTED'}\n";
		}
close(LOGFILE);
`rm con1.*`;
$time2=`date +"%s"`;
$time=$time2-$time1;
print "Total time: $time seconds\n";
exit(0);

sub check_one_file{

	$output = `cd $exec_path ;./imp $_[0] +infer +check -o:con1 $_[2] -m:$_[1] 2>&1`;		
	ver_out($_[2],$_[1],$output);
	$output1 = `cd $exec_path ;./imp $_[0] +infer +check -club:ConvexHull -o:con1 $_[2] -m:$_[1] 2>&1`;		
	print LOGFILE "\n ConvexHull";
	ver_out($_[2],$_[1],$output);
	$output2 = `cd $exec_path ;./imp $_[0] +infer +check -simplifyCAbst -o:con1 $_[2] -m:$_[1] 2>&1`;		
	print LOGFILE "\n simplifyCAbst";
	ver_out($_[2],$_[1],$output);
	$output = `cd $exec_path ;./imp con1.impt -infer +check 2>&1`;	
	if(($output !~ /[\n]\s*Pre\/Post checking...done/ ))#||($_[2] =~ "ERROR:" ))
				{print LOGFILE "!!!!!!!\t\t verifying the impt file (generated with : $_[2] -m:$_[1]), type checking not done\n";}
	$output = `cd $exec_path ;gcc con1.c Primitives.c 2>&1`;	
	if (($output =~ /: error:/)|| ($output =~ /ld returned 1 exit status/))
		{print LOGFILE "!!!!!!!\t\t $_[2] -m:$_[1] gcc compile error\n";}
}
sub ver_out{
			$aux = 0;
			print LOGFILE "\n";
			if ($_[2] =~ /[\n]\s*POSSIBLE[^\n]*[\n]\s*(\d+)/ ){
				print LOGFILE "\t m:$_[1] $_[0] $1 runtime tests\n";
				$aux = 1;
				}
			elsif($_[2] =~ /[\n]\s*POSSIBLE([^=\n]*)=/ ){
				print LOGFILE "\t m:$_[1] $_[0] possible $1\n";
				$aux = 1;
				}
			elsif($_[2] =~ /[\n]\s*POSSIBLE[^\n]*[\n]\s*/ ){
				print LOGFILE "\t m:$_[1] $_[0] seems no precond?\n";
				$aux = 1;
				}
			if($_[2] =~ /[\n]\s*SAFETY/ ){
				print LOGFILE "\t m:$_[1] $_[0] safety\n";
				$aux = 1;
				}
			if($_[2] =~ /[\n]\s*BUG/ ){
				print LOGFILE "\t m:$_[1] $_[0] bug\n";
				$aux = 1;
				}
			if(($_[2] !~ /[\n]\s*Pre\/Post checking...done/ ))#||($_[2] =~ "ERROR:" ))
				{print LOGFILE "!!!!!!!\t\t type checking not done\n";}
			if ($_[2] =~ /ERROR:/)
				{print LOGFILE "!!!!!!!\t\t unexpected error\n";}
			if ($_[2] =~ /Parse error/)
				{print LOGFILE "!!!!!!!\t\t Parse error\n";}
			if($aux==0){
				if ($_[2]!~ /openFile: does not exist/)
					{print LOGFILE "!!!!!o eroare de formatare: $_[0] m:$_[1] bug\n"}
			}
}
