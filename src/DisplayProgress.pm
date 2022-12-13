#!/usr/bin/env perl
use warnings;
use strict;
use POSIX;

# So every function doesn't need to loop up for length...
sub PrintProgress;
sub ClearProgress;

# Functions for setting global variables
sub InitProgressVars;

# Many functions for specific outs-put
sub ReportProgress;

# Before we get going, let's set a standardized character limit for status messages.
# Note that we go with a fairly large number to try to get at least one line of
# text-wrap. NEVERMIND, that causes the carriage-return to effectively work as a
# newline.
my $DispProg_line_len = 90;

# Variables that we'll want to have access to
my $DispProg_dirname;
my $DispProg_cpus;
my $DispProg_total_genes;




###############################################################
#
#  Functions: PrintProgress & ClearProgress
#
sub PrintProgress
{
    my $str = shift;
    $str = $str.' ' while (length($str) < $DispProg_line_len);
    print "$str\r";
}
sub ClearProgress { PrintProgress(' '); }




###############################################################
#
#  Function: InitMirageProgressVars
#
sub InitProgressVars
{
    my $progress_dirname = shift;
    my $num_cpus = shift;
    my $total_genes = shift;

    # Record the location of the progress alcove
    $DispProg_dirname = CreateDirectory($progress_dirname);

    # Copy over the number of cpus (requested -- still want to be careful!)
    $DispProg_cpus = $num_cpus;

    # How many genes are there, in total?
    $DispProg_total_genes = $total_genes;
    
}




###############################################################
#
#  Function: ReportProgress
#
sub ReportProgress
{
    my $data_str = shift;
    my @Data = split(/\|/,$data_str);

    # Field 0 is always the part of the program we're working on
    my $part = $Data[0];

    # If we're in a multi-threaded stage of the program, the reporter's thread ID
    # will be field 1
    my $threadID = 0;
    $threadID = $Data[1] if (scalar(@Data) > 1);
    
    my $status = "  Diviner: ";
    if ($part eq 'startup') {

	PrintProgress($status."Checking files and performing setup");
	
    } elsif ($part eq 'main-loop' && rand() < 0.3) {

	my $completed_genes = $Data[2];

	if ($threadID) {

	    open(my $ProgFile,'>',$DispProg_dirname.$threadID);
	    print $ProgFile "$completed_genes\n";
	    close($ProgFile);

	} else {

	    for (my $i=1; $i<$DispProg_cpus; $i++) {

		my $thread_prog_filename = $DispProg_dirname.$threadID; 
		if (-e $thread_prog_filename) {

		    open(my $ThreadProgress,'<',$thread_prog_filename);
		    my $thread_prog_count = <$ThreadProgress>;
		    close($ThreadProgress);
		    $thread_prog_count =~ /^(\d+)/;
		    $completed_genes += $1;
		    
		}
		
	    }

	    PrintProgress($status."$completed_genes of $DispProg_total_genes genes examined");
	    
	}
	
    } elsif ($part eq 'final') {

	PrintProgress($status."Performing final cleanup and data aggregation");
	print "\n"; # Bonus newline!
	system("rm -rf \"$DispProg_dirname\"");
	
    }
    
}







1; # EOF
