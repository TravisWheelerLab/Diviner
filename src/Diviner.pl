#!/usr/bin/env perl
use warnings;
use strict;
use POSIX;
use Cwd;
use Getopt::Long;
use Time::HiRes;

# I AM UNAVOIDABLE
sub GetScriptDir { return '.' if ($0 !~ /\//); $0 =~ /^(.+)\/[^\/]+$/; return $1; }
use lib GetScriptDir();
use Bureaucracy;
use DisplayProgress;

# Subroutines
sub PrintUsage;
sub DetailedUsage;
sub ParseArgs;
sub GetMappedSeqMSA;
sub ParseAFA;
sub SplitGTFIntoChrs;
sub CoordsToGTFHashKeys;
sub GTFHashKeyToFname;
sub RecordSplicedMSA;
sub RecordSplicedMap;
sub ReduceMSAToSpecies;
sub FindGhostExons;
sub FindAliQualityDrops;
sub RecordGhostMSAs;
sub GenMultiAliString;
sub GenQueryLiftString;
sub GatherBestLocalAlis;
sub LocalAlign;
sub GetB62Score;
sub MultiAminoSeqAli;
sub GenBEDOutFiles;
sub CollapseAndCountOverlaps;
sub RangesOverlap;
sub IsGTFAnnotated;
sub RecordHitsByPctID;


# Blosum-62 stuff
my @Blosum62
    = ( 4,  0, -2, -1, -2,  0, -2, -1, -1, -1, -1, -1, -1, -1, -1,  1, -1, -2, -3, -2,  0,
	0,  9, -3, -4, -2, -3, -3, -1, -3, -1, -1, -3, -3, -3, -3, -1, -1, -1, -2, -2,  0,
       -2, -3,  6,  2, -3, -1, -1, -3, -1, -4, -3,  1, -1,  0, -2,  0,  1, -3, -4, -3,  0,
       -1, -4,  2,  5, -3, -2,  0, -3,  1, -3, -2,  0, -1,  2,  0,  0,  0, -3, -3, -2,  0,
       -2, -2, -3, -3,  6, -3, -1,  0, -3,  0,  0, -3, -4, -3, -3, -2, -2, -1,  1,  3,  0,
        0, -3, -1, -2, -3,  6, -2, -4, -2, -4, -3, -2, -2, -2, -2,  0,  1,  0, -2, -3,  0,
       -2, -3,  1,  0, -1, -2,  8, -3, -1, -3, -2,  1, -2,  0,  0, -1,  0, -2, -2,  2,  0,
       -1, -1, -3, -3,  0, -4, -3,  4, -3,  2,  1, -3, -3, -3, -3, -2, -2,  1, -3, -1,  0,
       -1, -3, -1,  1, -3, -2, -1, -3,  5, -2, -1,  0, -1,  1,  2,  0,  0, -3, -3, -2,  0,
       -1, -1, -4, -3,  0, -4, -3,  2, -2,  4,  2, -3, -3, -2, -2, -2, -2,  3, -2, -1,  0,
       -1, -1, -3, -2,  0, -3, -2,  1, -1,  2,  5, -2, -2,  0, -1, -1, -1, -2, -1, -1,  0,
       -2, -3,  1,  0, -3,  0, -1, -3,  0, -3, -2,  6, -2,  0,  0,  1,  0, -3, -4, -2,  0,
       -1, -3, -1, -1, -4, -2, -2, -3, -1, -3, -2, -1,  7, -1, -2, -1,  1, -2, -4, -3,  0,
       -1, -3,  0,  2, -3, -2,  0, -3,  1, -2,  0,  0, -1,  5,  1,  0,  0, -2, -2, -1,  0,
       -1, -3, -2,  0, -3, -2,  0, -3,  2, -2, -1,  0, -2,  1,  5, -1, -1, -3, -3, -2,  0,
	1, -1,  0,  0, -2,  0, -1, -2,  0, -2, -1,  1, -1,  0, -1,  4,  1, -2, -3, -2,  0,
       -1, -1,  1,  0, -2,  1,  0, -2,  0, -2, -1,  0,  1,  0, -1,  1,  4, -2, -3, -2,  0,
	0, -1, -3, -2, -1, -3, -3,  3, -2,  1,  1, -3, -2, -2, -3, -2, -2,  4, -3, -1,  0,
       -3, -2, -4, -3,  1, -2, -2, -3, -3, -2, -1, -4, -4, -2, -3, -3, -3, -3, 11,  2,  0,
       -2, -2, -3, -2,  3, -3,  2, -1, -2, -1, -1, -2, -3, -1, -2, -2, -2, -1,  2,  7,  0,
	0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0);

my %AminoIndex
    = ('A', 0,'C', 1,'D', 2,'E', 3,'F', 4,'G', 5,'H', 6,'I', 7,'K', 8,'L', 9,
       'M',10,'N',11,'P',12,'Q',13,'R',14,'S',15,'T',16,'V',17,'W',18,'Y',19,'X',20);
    
my $b62_gap = -4;




##############
#            #
#   SCRIPT   #
#            #
##############



if (@ARGV < 2) {
    if (@ARGV == 1 && lc($ARGV[0]) =~ /\-help/) {
	DetailedUsage();
    }
    PrintUsage();
}


# Figure out what the location of the Mirage src directory is
my $location = $0;
$location =~ s/Diviner\.pl$//;


# Parse any commandline arguments
my $options_ref = ParseArgs();
my %Options = %{$options_ref};
my $num_cpus = $Options{cpus};
my $save_msas = $Options{savemsas}; # Do we want to write our spliced MSAs to files?
my $score_density_threshold = $Options{density};
my $bad_ali_cutoff = $Options{alicutoff};


# Find all the friends we're going to need inside Diviner
my $dependencies_ref = FindDependencies();
my %Dependencies = %{$dependencies_ref};


# We're going to need these friends
my $sindex  = $Dependencies{'sindex'};
my $sfetch  = $Dependencies{'sfetch'};
my $sstat   = $Dependencies{'sstat'};
my $tblastn = $Dependencies{'tblastn'};


# An astute observer will notice that these aren't the same settings as Quilter
# uses, which is because this isn't frickin' Quilter, geez.
# It's rad that our standardized filenames let us play like this!
$tblastn = $tblastn.' -outfmt 6 ';


# Confirm that the input directory looks like the real deal
my $input_dirname = ConfirmDirectory($ARGV[0]);
my $final_results_dirname = ConfirmDirectory($input_dirname.'Final-MSAs');
my $all_species_dirname = ConfirmDirectory($input_dirname.'Species-MSAs');


# Start off the real work by parsing the species guide, which will give
# us genome locations and chromosome lengths.
my $tildedir_check = OpenSystemCommand('echo ~');
my $tildedir = <$tildedir_check>;
$tildedir =~ s/\n|\r//g;
$tildedir = ConfirmDirectory($tildedir);
close($tildedir_check);


# Let the user know that we're getting to work
ReportProgress('startup');


my $SpeciesGuide = OpenInputFile($ARGV[1]);
my %SpeciesToGenomes;
my %SpeciesToGTF;
my %ChrLensBySpecies;
while (my $line = <$SpeciesGuide>) {

    $line =~ s/\n|\r//g;
    next if ($line !~ /(\S+)\s+(\S+)\s+(\S+)/);
    my $species = lc($1);
    my $genome = $2;
    my $gtf = $3;
    $genome =~ s/\~\//$tildedir/;
    $gtf =~ s/\~\//$tildedir/;

    $SpeciesToGenomes{$species} = $genome;

    # I don't know why we'd be at this point, where we have
    # Mirage results without a genome index, but just in case...
    if (!(-e $genome.'.hsi')) {
	print "\n";
	print "  Warning: Couldn't find existing 'hsi' index for genome file '$genome'\n";
	print "           Index creation may take a couple of seconds\n\n";
	RunSystemCommand($sindex.' '.$genome);
	print "  Indexing successful!\n\n";
    }

    # Get chromosome lengths for the genome
    my $SstatOut = OpenSystemCommand($sstat.' '.$genome);
    while (my $sstat_line = <$SstatOut>) {
	$sstat_line =~ s/\n|\r//g;
	if ($sstat_line =~ /^\: (\S+)\s+(\d+)/) {
	    my $chr = $1;
	    my $len = $2;
	    $ChrLensBySpecies{$species.'|'.$chr} = $len;
	}
    }
    close ($SstatOut);

    # There may not be a GTF for every species, but if there is
    # a GTF we'll want to know its name.
    if (-e $gtf) {
	$SpeciesToGTF{$species} = $gtf;
    }

}
close($SpeciesGuide);


# As a bit of a sanity-check, if we don't have any genomes then we bail
if (scalar(keys %SpeciesToGenomes) == 0) {
    die "\n  ERROR:  Failed to locate usable genome mappings in species guide file '$ARGV[1]'\n\n";
}


# We'll do a preliminary run through 'FinalMSAs' to compute the total number of
# genes, so that we can figure out how to allocate work for each of our processes.
my $FinalMSAs = OpenDirectory($final_results_dirname);
my @GeneList;
while (my $fname = readdir($FinalMSAs)) {
    next if ($fname !~ /(\S+)\.afa$/);
    push(@GeneList,$1);
}
closedir($FinalMSAs);


# Quick sanity check
if (scalar(@GeneList) == 0) {
    die "\n  ERROR:  No MSA files were found in '$final_results_dirname'...?\n\n";
}


# Are we asking for too many cpus?
$num_cpus = Min($num_cpus,scalar(@GeneList));


# Now that we know that we have solid inputs, we'll create the output directory
my $outdirname  = CreateDirectory($Options{outdirname});
my $outgenesdir = CreateDirectory($outdirname.'Results-by-Gene');
my $bedfilesdir = CreateDirectory($outdirname.'BED-Files');


# Things are looking good if we've made it this far without complaint,
# so let's provide a smidgen of feedback
InitProgressVars($outdirname.'.progress',$num_cpus,scalar(@GeneList));


# GTFs will let us know if the exons we uncover are known coding regions
# (as opposed to known exons that are simply missing from our database).
my $micro_gtfs_dirname = 0;
if (scalar(@GeneList) > 10) { # Don't break up the GTF for small inputs
    $micro_gtfs_dirname = CreateDirectory($outdirname.'Temp-GTF-Data');
    foreach my $species (keys %SpeciesToGTF) {
	SplitGTFIntoChrs($species,$SpeciesToGTF{$species});
    }
}
    

# Look away, children, the processes are spawning!
my $threadID = SpawnProcesses($num_cpus);


# I've been borned! What's my job?
my $thread_portion = int(scalar(@GeneList)/$num_cpus);
my $start_gene_id = $threadID * $thread_portion;
my $end_gene_id = (1+$threadID) * $thread_portion;
$end_gene_id = scalar(@GeneList) if ($threadID == $num_cpus-1);


# Name temporary filenames that we'll want to use (and, while we're at it,
# fill in all of the wild 'n' wacky tblastn arguments we'll be using).
my $nucl_seq_fname = $outgenesdir.'nucl.tmp.'.$threadID.'.fa';
my $prot_seq_fname = $outgenesdir.'prot.tmp.'.$threadID.'.fa';
my $tbn_out_fname  = $outgenesdir.'tbn.tmp.'.$threadID.'.out';
$tblastn = $tblastn.' -subject '.$nucl_seq_fname.' -query '.$prot_seq_fname;
$tblastn = $tblastn.' -out '.$tbn_out_fname.' 1>/dev/null 2>&1';


# TIME FOR THE MAIN EVENT!
#
# We'll do this the easiest (laziest) way, which will just be running
# through each of our final MSAs, loading in *only* those sequences
# which have mappings, and then reverse-engineering exon markers.
#
# Fun!
#
my $total_ghost_exons = 0;
my $total_ghosts_busted = 0;
for (my $gene_id=$start_gene_id; $gene_id<$end_gene_id; $gene_id++) {

    my $completed_genes = $gene_id - $start_gene_id;
    ReportProgress('main-loop|'.$threadID.'|'.$completed_genes);

    my $gene  = $GeneList[$gene_id];
    my $fname = $final_results_dirname.$gene.'.afa';

    # Pull in an MSA that's been (1) reduced to mapped sequences, and
    # (2) has splice site markers.
    my ($msa_ref,$mapmsa_ref,$seqnames_ref,$num_seqs,$msa_len,$speciestochrs_ref)
	= GetMappedSeqMSA($fname,$gene);

    # If we don't have anything to do with this family, skip to the next
    next if (!$msa_ref);
    
    my @MSA = @{$msa_ref};
    my @MapMSA = @{$mapmsa_ref};
    my @SeqNames = @{$seqnames_ref};
    my %SpeciesToChrs = %{$speciestochrs_ref};

    # At this point, it makes sense to create the result directory for this gene
    my $gene_outdir = CreateDirectory($outgenesdir.$gene);

    # Get your butt into this file, mister!
    RecordSplicedMSA(\@MSA,\@SeqNames,$num_seqs,$msa_len,$gene_outdir.'mapped-seqs.afa');

    # Now we'll reduce our MSA even further, down to just one sequence per
    # species!
    ($msa_ref,$mapmsa_ref,$seqnames_ref,$num_seqs)
	= ReduceMSAToSpecies(\@MSA,\@MapMSA,\@SeqNames,$num_seqs,$msa_len);
    @MSA = @{$msa_ref};
    @MapMSA = @{$mapmsa_ref};
    my @SpeciesNames = @{$seqnames_ref};
    my $num_species = $num_seqs;

    # Write these ones out, too!
    RecordSplicedMSA(\@MSA,\@SpeciesNames,$num_seqs,$msa_len,$gene_outdir.'species.afa');
    RecordSplicedMap(\@MSA,\@MapMSA,\@SpeciesNames,\%SpeciesToChrs,$num_seqs,$msa_len,$gene_outdir.'genome-mappings.out');
    
    # Now that we have our super-reduced splice-site-ified MSA, let's get real nasty
    # with it (by way of locating exons suggestive of "ghosts")!
    my ($num_ghost_exons, $num_ghosts_busted) =
	FindGhostExons($gene,\@MSA,\@MapMSA,\@SpeciesNames,$num_species,$msa_len,\%SpeciesToChrs);

    # Add onto our overarching tallies
    $total_ghost_exons += $num_ghost_exons;
    $total_ghosts_busted += $num_ghosts_busted;

    # If we didn't bust any ghosts, then there aren't any MSAs to build or
    # GTFs to examine... yay?
    next if (!$num_ghosts_busted);

    # Time to build some gorgeous translated MSAs!
    RecordGhostMSAs($gene);

}


# How'd I do?  I don't even know!
if ($threadID) {
    my $final_outf = OpenOutputFile($outgenesdir.$threadID.'.final-tally.out');
    print $final_outf "$total_ghosts_busted / $total_ghost_exons\n";
    close($final_outf);
}


# The age of threads is coming to a close!
if ($threadID) {
    exit(0);
}
while (wait() != -1) {}


# Let the user know they're in the home-stretch!
ReportProgress('final');


# Woo-hoo!  Janitorial work is my favorite!
for ($threadID=0; $threadID<$num_cpus; $threadID++) {

    # Clear out all these files we don't need
    $nucl_seq_fname = $outgenesdir.'nucl.tmp.'.$threadID.'.fa';
    $prot_seq_fname = $outgenesdir.'prot.tmp.'.$threadID.'.fa';
    $tbn_out_fname  = $outgenesdir.'tbn.tmp.'.$threadID.'.out';

    if (-e $nucl_seq_fname) { system("rm $nucl_seq_fname"); }
    if (-e $prot_seq_fname) { system("rm $prot_seq_fname"); }
    if (-e $tbn_out_fname)  { system("rm $tbn_out_fname");  }

    # How'd ya do, helper?
    if ($threadID) {
	
	my $final_infname = $outgenesdir.$threadID.'.final-tally.out';
	my $final_inf = OpenInputFile($final_infname);
    
	my $line = <$final_inf>;
	$line =~ /(\d+) \/ (\d+)/;
	$total_ghosts_busted += $1;
	$total_ghost_exons += $2;
	
	# Now erase every last trace of that darn helper from the Earth!
	close($final_inf);
	system("rm $final_infname");

    }

}


# This is what we call "the final judgment": did we find *anything*?
if ($total_ghost_exons == 0) {

    # Wowza yowza bo-bowza!  Really?  Nothing?  Okay...
    system("rm -rf $outdirname \&");
    print "\n  No potentially unannotated exons detected\n\n";

    exit(0);

}


# We'll aggregate our outputs into .bed files
GenBEDOutFiles();


# Clear out that stinky ol' GTF data directory!
RunSystemCommand("rm -rf \"$micro_gtfs_dirname\"") if (-d $micro_gtfs_dirname);


# Additionally, we'll write out the (easier on the eyes) file that lists
# each exon that we found, in order of percent alignment identity.
my $results_overview_str = RecordHitsByPctID();
print "\n$results_overview_str\n";


# THAT'S IT!
print "\n";
print "  Diviner complete; results in $outdirname\n";
print "\n\n";


1;






###################
#                 #
#   SUBROUTINES   #
#                 #
###################






###############################################################
#
#  Function: PrintUsage
#
sub PrintUsage
{
    print "\n";
    print "  USAGE :  ./Diviner.pl {OPT.s} [Mirage-Results] [Species-Guide]\n";
    print "\n";
    print "  OPT.s :  -cpus=[int]           : Number of compute cores\n";
    print "           -outdirname=[string]  : Name of the output directory\n";
    print "           -density=[double]     : BLOSUM-62 score density cutoff\n";
    die "\n";
}





###############################################################
#
#  Function: DetailedUsage
#
sub DetailedUsage
{
    print "\n";
    print "  USAGE :  ./Diviner.pl {OPT.s} [Mirage-Results] [Species-Guide]\n";
    print "\n";
    print "  OPT.s :  -cpus=[int]          : Set the number of CPU cores to use.\n";
    print "                                  (default:2)\n";
    print "\n";
    print "           -outdirname=[string] : Save program outputs to a directory with the specified name.\n";
    print "                                  (default:Diviner-Results)\n";
    print "\n";
    print "           -density=[double]    : Set the BLOSUM-62 score density threshold for acceptable\n";
    print "                                  alignments between known exons and possible coding regions.\n";
    print "\n";
    print "                                  Recommended range: 1 (distant homologs) to 3 (strong similarity)\n";
    print "                                  (default:1.5)\n";
    die "\n";
}





###############################################################
#
#  Function: ParseArgs
#
sub ParseArgs
{

    my %Options = (
	cpus => 1,
        outdirname => 'Diviner-Results',
        savemsas => 0,
	alicutoff => 0.4,
	density => 2
        );

    &GetOptions( 
        \%Options,
        "help",
	"cpus=i",
        "outdirname=s",
	"savemsas",
	"alicutoff=s",
	"density=s"
        )
        || die "\n  ERROR:  Failed to parse command line arguments\n\n";

    if ($Options{help}) {
	DetailedUsage();
    }

    return \%Options;
    
}




###############################################################
#
#  Function: GetMappedSeqMSA
#
sub GetMappedSeqMSA
{
    my $msa_infname = shift;
    my $gene = shift;

    # Start off by just reading in the MSA as-is
    my ($msa_ref,$seqnames_ref,$base_num_seqs,$base_msa_len) = ParseAFA($msa_infname);
    my @BaseMSA = @{$msa_ref};
    my @BaseSeqNames = @{$seqnames_ref};

    # Now we'll check each of the present species to see who in this
    # family is mapped.
    my %SpeciesToMapfiles;
    my %SpeciesToChr;
    my %MappedSeqs;
    foreach my $seqname (@BaseSeqNames) {

	# NOTE: We're currently assuming that our names are formatted in
	#       the Mirage-y way.
	# TODO: Change this to accept UniProt formatting
	$seqname =~ /^([^\|]+)\|/;
	my $species = lc($1);

	# If we've already pulled in this species' mapped sequences
	# (or confirmed that this whole species didn't map),
	# then skip right along, ya dinghus!
	next if ($SpeciesToMapfiles{$species});

	# Do we have a mapping file for this gene?
	my $mapfname = $all_species_dirname.$species.'/mappings/'.$gene.'.out';
	if (!(-e $mapfname)) {
	    $SpeciesToMapfiles{$species} = "-1";
	    next;
	}
	$SpeciesToMapfiles{$species} = $mapfname;

	# Oh boy! Time to read a file (right now, all we want is a roster
        # of mapped sequences)
	my $mapf = OpenInputFile($mapfname);
	my $canon_chr;
	while (my $line = <$mapf>) {

	    $line =~ s/\n|\r//g;

	    if ($line =~ /^Canonical Chromosome\: (\S+)/) {

		$canon_chr = $1;
		$SpeciesToChr{$species} = $canon_chr;
		
	    } elsif ($line =~ /^Sequence ID\: (\S+)/) {

		my $mapped_seqname = $1;

		# We'll need to make sure that we've hit on the right chromosome
		$line = <$mapf>; # map method
		$line = <$mapf>; # chromosome
		if ($line =~ /^Chromosome \: (\S+)/) {
		    my $mapped_chr = $1;
		    if ($mapped_chr eq $canon_chr) {
			$MappedSeqs{$mapped_seqname} = 1;
		    }
		}
		
	    }
	    
	}
	close($mapf);
	
    }

    
    # Before we go any further, if there's only one species mapping then we'll
    # bail.  Because 'SpeciesToMapfiles' initially has '-1' for any unmapped
    # species, we'll need to switch those to '0's
    my $num_mapped_species = 0;
    foreach my $species (keys %SpeciesToMapfiles) {
	if ($SpeciesToMapfiles{$species} eq "-1") {
	    $SpeciesToMapfiles{$species} = 0;
	} else {
	    $num_mapped_species++;
	}
    }
    return (0,0,0,0,0,0) if ($num_mapped_species <= 1);
    

    # Awesome!  Now we have a roster of sequences that mapped back to their
    # genomes, so let's take the initial step of reducing our MSA down to just
    # that collection.
    my @MSA;
    my @SeqNames;
    my $num_seqs = 0;
    for (my $i=0; $i<$base_num_seqs; $i++) {
	if ($MappedSeqs{$BaseSeqNames[$i]}) {

	    $SeqNames[$num_seqs] = $BaseSeqNames[$i];

	    for (my $j=0; $j<$base_msa_len; $j++) {
		$MSA[$num_seqs][$j] = $BaseMSA[$i][$j];
	    }
	    $num_seqs++;

	}
    }

    # We'll get rid of any all-gap columns to get our actual msa_len.
    # Note that this will clear any original '/' columns (if we're
    # looking at a dirty MSA), but that's fine since we're re-inserting them.
    my $msa_len = 0;
    for (my $j=0; $j<$base_msa_len; $j++) {
	my $residues = 0;
	for (my $i=0; $i<$num_seqs; $i++) {
	    if ($MSA[$i][$j] =~ /[A-Z]/) {
		$residues = 1;
		last;
	    }
	}
	if ($residues) {
	    for (my $i=0; $i<$num_seqs; $i++) {
		$MSA[$i][$msa_len] = $MSA[$i][$j];
	    }
	    $msa_len++;
	}
    }

    # Phew, that was some good MSA constructing!
    #
    # Next up will be associating each residue with its mapping coordinates
    # and determining where there ought to be splice site boundaries marked.
    #
    my @MapMSA;
    foreach my $species (keys %SpeciesToMapfiles) {

	next if (!$SpeciesToMapfiles{$species});

	my $mapf = OpenInputFile($SpeciesToMapfiles{$species});
	while (my $line = <$mapf>) {

	    # Fast-forward to the next canonically-mapped sequence
	    next if ($line !~ /Sequence ID\: (\S+)/);
	    my $seqname = $1;
	    next if (!$MappedSeqs{$seqname});

	    # We got a mappy boi!  Quick -- what row are you?
	    my $seq_row = 0;
	    while ($SeqNames[$seq_row] ne $seqname) {
		$seq_row++;
	    }

	    # How many exons does this sequence have?
	    $line = <$mapf>; # Map method
	    $line = <$mapf>; # Chromosome
	    $line = <$mapf>; # Num Exons!
	    $line =~ /Num Exons  \: (\d+)/;
	    my $num_exons = $1;

	    # We'll read in the full set of chromosome coordinates for
	    # this sequence before attributing them to MSA positions
	    # (just to simplify writing)
	    my $coord_list_str;
	    for (my $i=0; $i<$num_exons; $i++) {

		$line = <$mapf>; # Exon overview
		$line = <$mapf>; # Coords!

		$line =~ s/\n|\r//g;
		if ($coord_list_str) {
		    $coord_list_str = $coord_list_str.','.$line;
		} else {
		    $coord_list_str = $line;
		}
		
	    }

	    # Now we'll split up our coordinate list string into an
	    # array and walk along the MSA attributing each character
	    # to a coordinate
	    my @CoordList = split(/\,/,$coord_list_str);
	    my $next_coord = 0;
	    my $msa_pos = 0;
	    while ($msa_pos < $msa_len) {
		if ($MSA[$seq_row][$msa_pos] =~ /[A-Z]/) {
		    $MapMSA[$seq_row][$msa_pos] = $CoordList[$next_coord];
		    $next_coord++;
		} else {
		    $MapMSA[$seq_row][$msa_pos] = 0;
		}
		$msa_pos++;
	    }
	    

	}
	close($mapf);
	
    }

    
    # Well that sure gives us a 'MapMSA,' but what if we want to have a
    # splicey MSA?  Have no fear, sweet child, I'm gonna ruin you with
    # splice sites.

    
    # NOTE that the way we'll do this is by first identifying where there
    #   are positions in the MapMSA where the distance between two adjacent
    #   residues is >4, and recording all of those positions.
    my @LastCoord;
    for (my $i=0; $i<$num_seqs; $i++) {
	$LastCoord[$i] = 0;
    }
    
    # This will mark the first amino acid in each exon
    my %SpliceCols; 
    for (my $j=0; $j<$msa_len; $j++) {
	for (my $i=0; $i<$num_seqs; $i++) {
	    if ($MapMSA[$i][$j]) {
		if (abs($LastCoord[$i]-$MapMSA[$i][$j])>4) {
		    if ($SpliceCols{$j}) { $SpliceCols{$j}++; }
		    else                 { $SpliceCols{$j}=1; }
		}
		$LastCoord[$i] = $MapMSA[$i][$j];
	    }
	}
    }

    # Now we'll resolve any splice-sites that aren't universally agreed upon
    # by the sequences that have residues at the given positions.
    # We'll be (specifically) looking to discount columns where the
    # sequences who want the splice-site are immediately following a gap
    # (these look more like alt 3' splice sites), and then requiring that
    # the majority of non-gap-adjacent residues also call a given splice site.
    my @SpliceColList = sort {$a <=> $b} keys %SpliceCols;
    my @VetoedCols;
    my @VetoedColsVotes;
    for (my $splice_col_id=1; $splice_col_id<scalar(@SpliceColList); $splice_col_id++) { # '0' is mandatory

	my $splice_col = $SpliceColList[$splice_col_id];

	# How many sequences have a residue at *both* this column and the
	# last, and want it to be a splice site?
	my $paired_residue_for = 0;
	my $paired_residue_against = 0;
	for (my $i=0; $i<$num_seqs; $i++) {
	    if ($MSA[$i][$splice_col] =~ /[A-Z]/ && $MSA[$i][$splice_col-1] =~ /[A-Z]/) {

                # DEBUGGING
		if (!($MapMSA[$i][$splice_col] && $MapMSA[$i][$splice_col-1])) {
		    print "Mapping issue around col $splice_col in '$SeqNames[$i]'\n";
		    next;
		}
		
		if (abs($MapMSA[$i][$splice_col]-$MapMSA[$i][$splice_col-1])>4) {
		    $paired_residue_for++;
		} else {
		    $paired_residue_against++;
		}

	    }
	}

	# Has this splice site been vetoed?
	if ($paired_residue_against && $paired_residue_against >= $paired_residue_for) {
	    push(@VetoedCols,$splice_col);
	    push(@VetoedColsVotes,$SpliceCols{$splice_col});
	    $SpliceCols{$splice_col} = 0;
	    next;
	}
	
    }

    # If we had a run of vetoed columns that are close (1 or 2 residues apart) and
    # add up to majority support, then we'll re-introduce one of them into the list.
    my $run_start;
    my $run_end=1;
    while ($run_end < scalar(@VetoedCols)-1) {

	# Are we in a run of vetoed columns?
	$run_start = $run_end;
	$run_end++;
	my $run_votes = $VetoedColsVotes[$run_start];
	while ($run_end < scalar(@VetoedCols) && $VetoedCols[$run_end] - $VetoedCols[$run_end-1] < 3) {
	    $run_votes += $VetoedColsVotes[$run_end];
	    $run_end++;
	}

	# If there isn't a run of nearby vetoes, then we'll move right along
	next if ($run_end == $run_start+1);

	# Count the number of sequences that have non-gap characters
	# at one of the vetoed columns
	my $non_gappers = 0;
	for (my $i=0; $i<$num_seqs; $i++) {
	    for (my $col_id=$run_start; $col_id<$run_end; $col_id++) {
		my $msa_pos = $VetoedCols[$col_id];
		if ($MapMSA[$i][$msa_pos] || $MapMSA[$i][$msa_pos-1]) {
		    $non_gappers++;
		    last;
		}
	    }
	}

	# If enough columns have been vetoed to form a majority, then the most
	# used of the group will be designated a splice site.
	next if ($non_gappers >= $run_votes*2);

	my $top_veto_col = $run_start;
	my $top_veto_vote = $VetoedColsVotes[$run_start];
	for (my $i=$run_start+1; $i<$run_end; $i++) {
	    if ($top_veto_vote < $VetoedColsVotes[$i]) {
		$top_veto_col = $i;
		$top_veto_vote = $VetoedColsVotes[$i];
	    }
	}

	# THE PEOPLE HAVE SPOKEN!
	$SpliceCols{$top_veto_col} = $run_votes;
	
    }

    # Get the final list of splice site columns
    @SpliceColList = sort {$a <=> $b} keys %SpliceCols;

    # Now we construct the final splice-site-ified MSAs!
    my @SplicedMSA;
    my @SplicedMapMSA;
    my $spliced_msa_len = 0;
    my $splice_col_id = 0;
    for (my $j=0; $j<$msa_len; $j++) {

	# Have we hit our next splice column?
	if ($splice_col_id < scalar(@SpliceColList) && $SpliceColList[$splice_col_id] == $j) {
	    for (my $i=0; $i<$num_seqs; $i++) {
		$SplicedMSA[$i][$spliced_msa_len] = '/';
		$SplicedMapMSA[$i][$spliced_msa_len] = 0;
	    }
	    $spliced_msa_len++;
	    $splice_col_id++;
	}

	for (my $i=0; $i<$num_seqs; $i++) {
	    $SplicedMSA[$i][$spliced_msa_len] = $MSA[$i][$j];
	    $SplicedMapMSA[$i][$spliced_msa_len] = $MapMSA[$i][$j];
	}
	$spliced_msa_len++;

    }

    # Finally, round things out with a splice site column
    for (my $i=0; $i<$num_seqs; $i++) {
	$SplicedMSA[$i][$spliced_msa_len] = '/';
	$SplicedMapMSA[$i][$spliced_msa_len] = 0;
    }
    $spliced_msa_len++;

    # Pass everything we got back on up the chain of command!
    return (\@SplicedMSA,\@SplicedMapMSA,\@SeqNames,$num_seqs,$spliced_msa_len,\%SpeciesToChr);
    
}





###############################################################
#
#  Function: ParseAFA
#
sub ParseAFA
{
    my $fname = shift;

    my $inf = OpenInputFile($fname);
    my $num_seqs = -1;
    my $msa_len;
    my @MSA;
    my @SeqNames;
    while (my $line = <$inf>) {

	$line =~ s/\n|\r//g;
	next if (!$line);

	if ($line =~ /\>(\S+)/) {

	    my $seqname = $1;
	    push(@SeqNames,$seqname);
	    $num_seqs++;
	    $msa_len = 0;

	} else {

	    foreach my $char (split(//,$line)) {
		$MSA[$num_seqs][$msa_len] = uc($char);
		$msa_len++;
	    }

	}
	
    }
    close($inf);

    $num_seqs++;

    return(\@MSA,\@SeqNames,$num_seqs,$msa_len);

}







###############################################################
#
#  Function: SplitGTFIntoChrs
#
sub SplitGTFIntoChrs
{
    my $species = shift;
    my $gtf_fname = shift;

    my %MicroGTFNames;
    my %MicroGTFs;
    
    my $GTF = OpenInputFile($gtf_fname);
    while (my $line = <$GTF>) {

	next if ($line !~ /^\s*(\S+)\s+\S+\s+(\S+)\s+(\d+)\s+(\d+)\s+\S+\s+(\S+)/);

	my $gtf_chr    = $1;
	my $gtf_type   = lc($2);
	my $gtf_start  = $3;
	my $gtf_end    = $4;
	my $gtf_strand = $5;

	if ($gtf_type ne 'cds' && $gtf_type ne 'exon') { next; }

	foreach my $hash_key (CoordsToGTFHashKeys($gtf_start,$gtf_end,$gtf_chr,$gtf_strand)) {

	    my $micro_gtf_fname = GTFHashKeyToFname($species,$hash_key);

	    if (!$MicroGTFNames{$micro_gtf_fname}) {
		$MicroGTFNames{$micro_gtf_fname} = 1;
		$MicroGTFs{$micro_gtf_fname} = OpenOutputFile($micro_gtf_fname);
	    }
	    my $MicroGTF = $MicroGTFs{$micro_gtf_fname};

	    if ($gtf_strand eq '+') { print $MicroGTF "$gtf_start..$gtf_end\n"; }
	    else                    { print $MicroGTF "$gtf_end..$gtf_start\n"; }

	}

    }
    close($GTF);

    foreach my $micro_gtf_fname (keys %MicroGTFNames) {
	close($MicroGTFs{$micro_gtf_fname});
    }
    
}







###############################################################
#
#  Function: CoordsToGTFHashKeys
#
sub CoordsToGTFHashKeys
{
    my $start_coord = shift;
    my $end_coord   = shift;
    my $chromosome  = shift;
    my $strand      = shift;

    my $bases_per_index = 1000000; # 1 Mb per index
    my $start_index = int($start_coord / $bases_per_index);
    my $end_index   = int($end_coord   / $bases_per_index);

    my $key1 = $chromosome.$strand.$start_index;
    my $key2 = $chromosome.$strand.$end_index;

    if ($key1 eq $key2) {
	return ($key1);
    } else {
	return ($key1,$key2);
    }
    
}







###############################################################
#
#  Function: GTFHashKeyToFname
#
sub GTFHashKeyToFname
{
    my $species = shift;
    my $hash_key = shift;
    $hash_key =~ /^(\S+[\+|\-])(\d+)$/;

    my $fname = $micro_gtfs_dirname.$species.'.'.$1.'.'.$2.'.out';

    return $fname;
    
}







###############################################################
#
#  Function: RecordSplicedMSA
#
sub RecordSplicedMSA
{

    my $msa_ref = shift;
    my $seqnames_ref = shift;
    my $num_seqs = shift;
    my $msa_len = shift;
    my $outfname = shift;

    my @MSA = @{$msa_ref};
    my @SeqNames = @{$seqnames_ref};
    
    my $outf = OpenOutputFile($outfname);
    for (my $i=0; $i<$num_seqs; $i++) {

	print $outf ">$SeqNames[$i]\n";
	for (my $j=0; $j<$msa_len; $j++) {
	    print $outf "$MSA[$i][$j]";
	    print $outf "\n" if (($j+1) % 60 == 0);
	}
	print $outf "\n" if ($msa_len % 60);
	#print $outf "\n";
	
    }
    close($outf);

}




###############################################################
#
#  Function: RecordSplicedMap
#
sub RecordSplicedMap
{

    my $msa_ref = shift;
    my $map_msa_ref = shift;
    my $species_names_ref = shift;
    my $species_to_chrs_ref = shift;
    my $num_species = shift;
    my $msa_len = shift;
    my $outfname = shift;

    my @MSA = @{$msa_ref};
    my @MapMSA = @{$map_msa_ref};
    my @SpeciesNames = @{$species_names_ref};
    my %SpeciesToChrs = %{$species_to_chrs_ref};
    
    my $outf = OpenOutputFile($outfname);
    for (my $i=0; $i<$num_species; $i++) {

	my $species = $SpeciesNames[$i];
	my $chr = $SpeciesToChrs{$species};

	my @ExonMaps;
	my $num_exons = 0;
	my $exon_maps_str = '';
	for (my $j=0; $j<$msa_len; $j++) {

	    next if ($MSA[$i][$j] eq '-');

	    if ($MSA[$i][$j] eq '/') {
		if ($exon_maps_str) {
		    push(@ExonMaps,$exon_maps_str);
		    $num_exons++;
		}
		$exon_maps_str = '';
	    } elsif ($exon_maps_str) {
		$exon_maps_str = $exon_maps_str.','.$MapMSA[$i][$j];
	    } else {
		$exon_maps_str = $MapMSA[$i][$j];
	    }
	    
	}

	print $outf "Species    : $species\n";
	print $outf "Chromosome : $chr\n";
	print $outf "Num Exons  : $num_exons\n";

	my $species_num_aminos = 0;
	for (my $j=0; $j<$num_exons; $j++) {

	    $species_num_aminos++;

	    my $exon_map_str = $ExonMaps[$j];

	    $exon_map_str =~ /^(\d+)/;
	    my $start_nucl = $1;

	    $exon_map_str =~ /(\d+)$/;
	    my $end_nucl = $1;

	    print $outf "* Aminos $species_num_aminos..";
	    $species_num_aminos += scalar(split(/\,/,$exon_map_str))-1;
	    print $outf "$species_num_aminos, $chr:$start_nucl..$end_nucl\n";

	    print $outf "$exon_map_str\n";
	    
	}

	print $outf "\n";
	
    }
    close($outf);

}





###############################################################
#
#  Function: ReduceMSAToSpecies
#
sub ReduceMSAToSpecies
{
    my $msa_ref = shift;
    my $mapmsa_ref = shift;
    my $seqnames_ref = shift;
    my $num_seqs = shift;
    my $msa_len = shift;

    my @MSA = @{$msa_ref};
    my @MapMSA = @{$mapmsa_ref};
    my @SeqNames = @{$seqnames_ref};

    # First off, who are our species?  Which sequences belong to which species?
    my %SpeciesToSeqIDs;
    for (my $i=0; $i<$num_seqs; $i++) {
	$SeqNames[$i] =~ /^([^\|]+)\|/;
	my $species = $1;
	if ($SpeciesToSeqIDs{$species}) {
	    $SpeciesToSeqIDs{$species} = $SpeciesToSeqIDs{$species}.','.($i+1);
	} else {
	    $SpeciesToSeqIDs{$species} = ($i+1);
	}
    }

    # Alrighty! Let's get reducing!
    my @SpeciesNames;
    my @SpeciesMSA;
    my @SpeciesMapMSA;
    my $num_species = 0;
    foreach my $species (keys %SpeciesToSeqIDs) {

	push(@SpeciesNames,$species);

	# Get the sequence IDs for every member of this species.
	# Note that we'll need to decrement by one because we previously
	# had to increment by one (to not throw out sequence '0')
	my @SeqIDs = split(/\,/,$SpeciesToSeqIDs{$species});
	for (my $i=0; $i<scalar(@SeqIDs); $i++) {
	    $SeqIDs[$i] = $SeqIDs[$i]-1;
	}

	# Great!  Now it's time to get reducing!  To do this, we'll just
	# walk along the MSA, and wherever there's a residue-containing
	# column we'll take a poll of what the residue should be, and majority
	# wins
	for (my $j=0; $j<$msa_len; $j++) {

	    # If this is a splice-site column, we can take it super easy
	    if ($MSA[0][$j] eq '/') {
		$SpeciesMSA[$num_species][$j] = '/';
		$SpeciesMapMSA[$num_species][$j] = 0;
		next;
	    }
	    
	    my %Residues;
	    foreach my $seq_id (@SeqIDs) {
		if ($MSA[$seq_id][$j] =~ /[A-Z]/) {
		    if ($Residues{$MSA[$seq_id][$j]}) {
			$Residues{$MSA[$seq_id][$j]}++;
		    } else {
			$Residues{$MSA[$seq_id][$j]}=1;
		    }
		}
	    }

	    # If this is a gap column, we can take it sorta easy
	    if (scalar(keys %Residues) == 0) {
		$SpeciesMSA[$num_species][$j] = '-';
		$SpeciesMapMSA[$num_species][$j] = 0;
		next;
	    }

	    # Alrighty then, who's the lucky residue?
	    my @ResidueList = keys %Residues;
	    my $top_residue = $ResidueList[0];
	    my $top_residue_count = $Residues{$top_residue};
	    for (my $i=1; $i<scalar(@ResidueList); $i++) {
		if ($Residues{$ResidueList[$i]} > $top_residue_count) {
		    $top_residue = $ResidueList[$i];
		    $top_residue_count = $Residues{$top_residue};
		}
	    }

	    # Great stuff!  Now, we just need to get a mapping coordinate from
	    # someone who used the top residue.
	    my $map_coord;
	    foreach my $seq_id (@SeqIDs) {
		if ($MSA[$seq_id][$j] eq $top_residue) {
		    $map_coord = $MapMSA[$seq_id][$j];
		    last;
		}
	    }

	    # Record that residue and mapping coordinate!
	    $SpeciesMSA[$num_species][$j] = $top_residue;
	    $SpeciesMapMSA[$num_species][$j] = $map_coord;
	    
	}

	# Another species in the bag!
	$num_species++;

    }

    # That was too easy!
    return(\@SpeciesMSA,\@SpeciesMapMSA,\@SpeciesNames,$num_species);
    
}





###############################################################
#
#  Function: FindGhostExons
#
sub FindGhostExons
{
    my $gene = shift;
    my $msa_ref = shift;
    my $mapmsa_ref = shift;
    my $speciesnames_ref = shift;
    my $num_species = shift;
    my $msa_len = shift;
    my $speciestochrs_ref = shift;

    my @MSA = @{$msa_ref};
    my @MapMSA = @{$mapmsa_ref};
    my @SpeciesNames = @{$speciesnames_ref};
    my %SpeciesToChrs = %{$speciestochrs_ref};

    # This probably seems *really* dumb, but we're going to enumerate the
    # ungapped position of each amino in each species' MSA
    my @IndexMSA;
    my @SpeciesNumAminos;
    for (my $i=0; $i<$num_species; $i++) {
	my $amino_index=0;
	for (my $j=0; $j<$msa_len; $j++) {
	    if ($MSA[$i][$j] =~ /[A-Za-z]/) {
		$IndexMSA[$i][$j] = ++$amino_index;
	    } else {
		$IndexMSA[$i][$j] = 0;
	    }
	}
	$SpeciesNumAminos[$i] = $amino_index;
    }

    # We're also going to find the limit values for each species' coding region
    my @CodingStarts;
    my @CodingEnds;
    for (my $i=0; $i<$num_species; $i++) {

	for (my $j=0; $j<$msa_len; $j++) {
	    if ($MapMSA[$i][$j] != 0) {
		$CodingStarts[$i] = $MapMSA[$i][$j];
		last;
	    }
	}

	for (my $j=$msa_len-1; $j>=0; $j--) {
	    if ($MapMSA[$i][$j] != 0) {
		$CodingEnds[$i] = $MapMSA[$i][$j];
		last;
	    }
	}

    }

    # First off, let's figure out where the starts (inclusive) and ends (exclusive)
    # of our exons are, as well as how many exons we have
    my @ExonStarts;
    my @ExonEnds;
    my $num_exons = 0;
    for (my $j=0; $j<$msa_len; $j++) {
	if ($MSA[0][$j] eq '/') {
	    $num_exons++;
	    push(@ExonEnds,$j) if ($j);
	    push(@ExonStarts,$j+1) if ($j+1 < $msa_len);
	}
    }
    $num_exons--; # We'll have overcounted by one, but that's okie-dokie

    # We'll also want to know how to recover species indices from their names, so...
    my %SpeciesToIndex;
    for (my $i=0; $i<$num_species; $i++) {
	$SpeciesToIndex{$SpeciesNames[$i]} = $i+1;
    }

    # Before we get into the nastiness, we'll set some variables to represent the
    # minimum number of amino acids for 'using an exon' and the maximum number
    # of amino acids for 'not using an exon' -- both Inclusive
    #
    # This is intended to pre-empt any occurrences of micro-exons or other
    # weird nonstandard splicing events that might cause an exon to technically
    # have amino acids in it, but clearly only as an artifact of computation.
    #
    # Similarly, we have a minimum number of aminos for a sequence to be worth
    # tblastn-ing.
    my $min_use_aminos = 6;
    my $max_nonuse_aminos = 3;
    my $min_search_aminos = 10;

    # Alright, now for the pain!  We'll do a pairwise comparison of species,
    # seeing which species suggest ghost exons in which other ones.
    # Wherever we find such pairs, we'll record (1) the sequence we're
    # looking for, (2) the species we're looking for it in, (3) the range
    # we're looking for it in, and (4) the species we found it in.
    my @QuerySeqs;
    my @QuerySpecies;
    my @QueryAminoRanges;
    my @TargetSpecies;
    my @TargetNuclRanges;
    my @MSAExons;
    for (my $s1=0; $s1<$num_species-1; $s1++) {
	for (my $s2=$s1+1; $s2<$num_species; $s2++) {

	    # <0 -> Bad
	    #  0 -> Unused
	    #  1 -> Good
	    my @ExonAliQuality;
	    my @IsMicroExon;
	    my @ExonS1Query;
	    my @ExonS2Query;
	    my @ExonS1FirstIndex;
	    my @ExonS2FirstIndex;
	    my @ExonS1LastIndex;
	    my @ExonS2LastIndex;

	    # Generate our exon-by-exon data for this species pair
	    for (my $exon_id=0; $exon_id<$num_exons; $exon_id++) {

		# Set all of our arrays to their default value for
		# this exon
		$ExonAliQuality[$exon_id] = 0;
		$IsMicroExon[$exon_id] = 0;
		$ExonS1Query[$exon_id] = '';
		$ExonS2Query[$exon_id] = '';
		$ExonS1FirstIndex[$exon_id] = 0;
		$ExonS2FirstIndex[$exon_id] = 0;
		$ExonS1LastIndex[$exon_id] = 0;
		$ExonS2LastIndex[$exon_id] = 0;

		my $s1_query = '';
		my $s2_query = '';
		my $num_match_cols    = 0;
		my $num_mismatch_cols = 0;
		my $num_s1_gaps       = 0; # species 1 has a gap, species 2 has an amino
		my $num_s2_gaps       = 0; #         2                    1
		for (my $col=$ExonStarts[$exon_id]; $col<$ExonEnds[$exon_id]; $col++) {

		    my $s1_char = uc($MSA[$s1][$col]);
		    my $s2_char = uc($MSA[$s2][$col]);

		    # Both are gaps -- nothing to see here!
		    if ($s1_char eq '-' && $s2_char eq '-') {
			next;
		    }

		    # Basic string buildup
		    if ($s1_char =~ /[A-Z]/) {
			$s1_query = $s1_query.$s1_char;
			$ExonS1FirstIndex[$exon_id] = $col
			    if (!$ExonS1FirstIndex[$exon_id]);
			$ExonS1LastIndex[$exon_id] = $col;
		    }

		    if ($s2_char =~ /[A-Z]/) {
			$s2_query = $s2_query.$s2_char;
			$ExonS2FirstIndex[$exon_id] = $col
			    if (!$ExonS2FirstIndex[$exon_id]);
			$ExonS2LastIndex[$exon_id] = $col;
		    }

		    
		    if ($s1_char eq $s2_char) {
			$num_match_cols++;
			next;
		    }

		    if ($s1_char eq '-') {
			$num_s1_gaps++;
			next;
		    }

		    if ($s2_char eq '-') {
			$num_s2_gaps++;
			next;
		    }

		    $num_mismatch_cols++;
		    
		}

		$ExonS1Query[$exon_id] = $s1_query;
		$ExonS2Query[$exon_id] = $s2_query;

		my $num_bad_cols     = $num_mismatch_cols + $num_s1_gaps + $num_s2_gaps;
		my $num_content_cols = $num_match_cols + $num_bad_cols;

		# If each species only had gaps, there's nothing to do here
		next if ($num_content_cols == 0);

		# We want to be aware if this is a micro-exon
		$IsMicroExon[$exon_id] = 1 if ($num_content_cols <= 3);

		# Overall alignment percent identity
		my $match_pct_id = 0.0; # Of columns where we have two aminos aligned, how many are identical?
		if ($num_match_cols+$num_mismatch_cols > 0) {
		    $match_pct_id = (100.0 * $num_match_cols / ($num_mismatch_cols+$num_match_cols)) / 100.0;
		}

		# Check 1: Low match percent identity
		if ($match_pct_id < $bad_ali_cutoff) {
		    $ExonAliQuality[$exon_id] = -1;
		    next;
		}

		# Check 2: Too many gaps
		if ($num_s1_gaps + $num_s2_gaps > $num_content_cols / 4) {
		    $ExonAliQuality[$exon_id] = -2;
		    next;
		}

		# All checks passed -- that's a nice exon alignment you
		# got there, bud!
		$ExonAliQuality[$exon_id] = 1;

	    }


	    # Now we can run along and figure out which exons we want to
	    # try hunting for!
	    for (my $exon_id=0; $exon_id<$num_exons; $exon_id++) {
		
		# We only want a low-quality exon!
		next if ($ExonAliQuality[$exon_id] >= 0);

		
		# Well well well, do we have enough amino acids from
		# species 1 to search its exon against the target range
		# from species 2?
		if (length($ExonS2Query[$exon_id]) >= $min_search_aminos) {

		    my $query_amino_seq = $ExonS2Query[$exon_id];

		    # Species 2 query amino acid range
		    my $query_start_amino_index = $IndexMSA[$s2][$ExonS2FirstIndex[$exon_id]];
		    my $query_end_amino_index = $IndexMSA[$s2][$ExonS2LastIndex[$exon_id]];

		    # Species 1 target nucleotide range
		    my $upstream_nucl_s1   = '[start-of-coding-region:'.$CodingStarts[$s1].']';
		    my $downstream_nucl_s1 = '[end-of-coding-region:'.$CodingEnds[$s1].']';
		    
		    my $scanner_exon_id = $exon_id-1;
		    while ($scanner_exon_id >= 0) {

			# Slurp in micro-exons
			if ($IsMicroExon[$scanner_exon_id]) {
			    if (length($ExonS2Query[$scanner_exon_id]) > 0) {

				$query_amino_seq = $ExonS2Query[$scanner_exon_id].$query_amino_seq;
				$query_start_amino_index = $IndexMSA[$s2][$ExonS2FirstIndex[$scanner_exon_id]];
			    }
			    $scanner_exon_id--;
			    next;
			}
			
			# Have we found an exon to define our upstream nucl. bound?
			if ($ExonAliQuality[$scanner_exon_id] == 1 && $ExonS1LastIndex[$scanner_exon_id]) {
			    $upstream_nucl_s1 = $MapMSA[$s1][$ExonS1LastIndex[$scanner_exon_id]];
			    last;
			}
			
			$scanner_exon_id--;

		    }
		    
		    $scanner_exon_id = $exon_id+1;
		    while ($scanner_exon_id < $num_exons) {
			
			# Slurp in micro-exons
			if ($IsMicroExon[$scanner_exon_id]) {
			    if (length($ExonS2Query[$scanner_exon_id]) > 0) {

				$query_amino_seq = $query_amino_seq.$ExonS2Query[$scanner_exon_id];
				$query_end_amino_index = $IndexMSA[$s2][$ExonS2LastIndex[$scanner_exon_id]];
			    }
			    $scanner_exon_id++;
			    next;
			}
			
			# Have we found an exon to define our downstream nucl. bound?
			if ($ExonAliQuality[$scanner_exon_id] == 1 && $ExonS1FirstIndex[$scanner_exon_id]) {
			    $downstream_nucl_s1 = $MapMSA[$s1][$ExonS1FirstIndex[$scanner_exon_id]];
			    last;
			}

			$scanner_exon_id++;
			
		    }
		    
		    my $s2_amino_range = $query_start_amino_index.'..'.$query_end_amino_index;
		    my $s1_nucl_range = $upstream_nucl_s1.'..'.$downstream_nucl_s1;

		    # Scream and shout about it, why don't'cha?!
		    push(@QuerySeqs,lc($query_amino_seq));
		    push(@QuerySpecies,$SpeciesNames[$s2]);
		    push(@QueryAminoRanges,$s2_amino_range);
		    push(@TargetSpecies,$SpeciesNames[$s1]);
		    push(@TargetNuclRanges,$s1_nucl_range);
		    push(@MSAExons,$exon_id);
		    
		}

		
		# Alrighty, then, do we have enough amino acids from
		# species 1 to search its exon against the target range
		# from species 2?
		if (length($ExonS1Query[$exon_id]) >= $min_search_aminos) {
			
		    my $query_amino_seq = $ExonS1Query[$exon_id];

		    # Species 1 query amino acid range
		    my $query_start_amino_index = $IndexMSA[$s1][$ExonS1FirstIndex[$exon_id]];
		    my $query_end_amino_index = $IndexMSA[$s1][$ExonS1LastIndex[$exon_id]];
		    
		    # Species 2 target nucleotide range
		    my $upstream_nucl_s2   = '[start-of-coding-region:'.$CodingStarts[$s2].']';
		    my $downstream_nucl_s2 = '[end-of-coding-region:'.$CodingEnds[$s2].']';
		    
		    my $scanner_exon_id = $exon_id-1;
		    while ($scanner_exon_id >= 0) {

			# Slurp in micro-exons
			if ($IsMicroExon[$scanner_exon_id]) {
			    if (length($ExonS1Query[$scanner_exon_id]) > 0) {

				$query_amino_seq = $ExonS1Query[$scanner_exon_id].$query_amino_seq;
				$query_start_amino_index = $IndexMSA[$s1][$ExonS1FirstIndex[$scanner_exon_id]];
			    }
			    $scanner_exon_id--;
			    next;
			}

			# Have we found an exon to define our upstream nucl. bound?
			if ($ExonAliQuality[$scanner_exon_id] == 1 && $ExonS2LastIndex[$scanner_exon_id]) {
			    $upstream_nucl_s2 = $MapMSA[$s2][$ExonS2LastIndex[$scanner_exon_id]];
			    last;
			}
			
			$scanner_exon_id--;

		    }
		    
		    $scanner_exon_id = $exon_id+1;
		    while ($scanner_exon_id < $num_exons) {
			
			# Slurp in micro-exons
			if ($IsMicroExon[$scanner_exon_id]) {
			    if (length($ExonS1Query[$scanner_exon_id]) > 0) {

				$query_amino_seq = $query_amino_seq.$ExonS1Query[$scanner_exon_id];
				$query_end_amino_index = $IndexMSA[$s1][$ExonS1LastIndex[$scanner_exon_id]];
			    }
			    $scanner_exon_id++;
			    next;
			}
			
			# Have we found an exon to define our downstream nucl. bound?
			if ($ExonAliQuality[$scanner_exon_id] == 1 && $ExonS2FirstIndex[$scanner_exon_id]) {
			    $downstream_nucl_s2 = $MapMSA[$s2][$ExonS2FirstIndex[$scanner_exon_id]];
			    last;
			}

			$scanner_exon_id++;
			
		    }
		    
		    my $s1_amino_range = $query_start_amino_index.'..'.$query_end_amino_index;
		    my $s2_nucl_range = $upstream_nucl_s2.'..'.$downstream_nucl_s2;

		    # Scream and shout about it, why don't'cha?!
		    push(@QuerySeqs,lc($query_amino_seq));
		    push(@QuerySpecies,$SpeciesNames[$s1]);
		    push(@QueryAminoRanges,$s1_amino_range);
		    push(@TargetSpecies,$SpeciesNames[$s2]);
		    push(@TargetNuclRanges,$s2_nucl_range);
		    push(@MSAExons,$exon_id);
		    
		}
		
	    }

	}
	
    }

    my $num_ghost_exons = scalar(@QuerySeqs);

    
    # I tried so hard, and got so far, but in the end it still mattered just a lil' bit
    return (0,0) if ($num_ghost_exons == 0);
    
    # NOICE!  Time to get ready for some good 'n' nasty tblastn-ery!

    # We'll tally up the number of successes
    my $ghosts_busted = 0;

    # Prepare to write some stuff to a file!
    my $outf = OpenOutputFile($outgenesdir.$gene.'/search.out');

    # We'll just go hit-by-hit, because that's what's sensible.
    for (my $ghost_id=0; $ghost_id<$num_ghost_exons; $ghost_id++) {

	# Write out the protein sequence to our protein sequence file.
	# We don't use my fancy file functions here because we'll be overwriting.
	open(my $protf,'>',$prot_seq_fname);
	print $protf ">seq\n$QuerySeqs[$ghost_id]\n\n";
	close($protf);

	# What's our search chromosome? What are our nucleotide coords?
	my $target_species = $TargetSpecies[$ghost_id];
	my $chr = $SpeciesToChrs{$target_species};
	my $revcomp = 0;
	if ($chr =~ /\[revcomp\]/) {
	    $chr =~ s/\[revcomp\]//;
	    $revcomp = 1;
	}

	$TargetNuclRanges[$ghost_id] =~ /^([^\.\.]+)\.\.(\S+)$/;
	my $target_start = $1;
	my $target_end = $2;

	# If we're at either terminii of our sequence, pull in an extra 25k
	# (or much as we can)
	my $terminal_search_dist = 25000;
	if ($target_start =~ /\:(\d+)/) {
	    my $seq_start = $1;
	    if ($revcomp) {
		$target_start = Min($seq_start+$terminal_search_dist,$ChrLensBySpecies{$target_species.'|'.$chr});		
	    } else {
		$target_start = Max($seq_start-$terminal_search_dist,1);
	    }
	}
	
	if ($target_end =~ /\:(\d+)/) {
	    my $seq_end = $1;
	    if ($revcomp) {
		$target_end = Max($seq_end-$terminal_search_dist,1);
	    } else {
		$target_end = Min($seq_end+$terminal_search_dist,$ChrLensBySpecies{$target_species.'|'.$chr});
	    }
	}

	
	# In case this is a large sequence window, we'll break up our
	# tblastn searching into 100kb sub-ranges
	my @HitAminoStarts;
	my @HitAminoEnds;
	my @HitNuclStarts;
	my @HitNuclEnds;
	my @HitEVals;
	my $num_tbn_hits = 0;
	my $sub_range_size = 100000;
	for (my $sub_range_low = Min($target_start,$target_end);
	     $sub_range_low < Max($target_start,$target_end);
	     $sub_range_low += $sub_range_size) {

	    my $sub_range_high = Min($sub_range_low+$sub_range_size,
				     Max($target_start,$target_end));

	    my $sub_range = $sub_range_low.'..'.$sub_range_high;
	    if ($target_start > $target_end) {
		$sub_range = $sub_range_high.'..'.$sub_range_low;
	    }
	    
	    # Well, we sure know what sequence to pull in now, don't we!
	    my $sfetch_cmd = $sfetch.' -range '.$sub_range;
	    $sfetch_cmd = $sfetch_cmd.' '.$SpeciesToGenomes{$target_species}.' '.$chr;
	    $sfetch_cmd = $sfetch_cmd.' > '.$nucl_seq_fname;
	    RunSystemCommand($sfetch_cmd);
	    
	    # Because of the wonders of filename standardization, we can do this!
	    RunSystemCommand($tblastn);

	    # In case of redundancy...
	    my @PrevUsedRegions;
	    
	    # What did we get?
	    my $tbnf = OpenInputFile($tbn_out_fname);
	    while (my $line = <$tbnf>) {
		if ($line) {
		    
		    my @HitData = split(/\s+/,$line);
		    my $amino_start = $HitData[6];
		    my $amino_end   = $HitData[7];
		    my $nucl_start  = $HitData[8];
		    my $nucl_end    = $HitData[9];
		    my $e_val       = $HitData[10];
		    
		    # We'll take notice of any hits with an e-val with a '-'
		    next if ($e_val !~ /e\-/);
		    
		    # What are the actual nucleotide coords?
		    if ($revcomp) {
			$nucl_start = $sub_range_high - $nucl_start;
			$nucl_end   = $sub_range_high - $nucl_end;
		    } else {
			$nucl_start += $sub_range_low;
			$nucl_end   += $sub_range_low;
		    }
		    my $nucl_range = $nucl_start.'..'.$nucl_end;
		    
		    # We need to confirm that this isn't overlapping with any of
		    # the nucleotide regions that have been previously used to
		    # map this sequence.
		    # It also can't fully contain an exon, ding-dong!
		    my $was_prev_used = 0;
		    my $prev_use_range_ref; # dummy var
		    foreach my $prev_used_region (@PrevUsedRegions) {
			($was_prev_used,$prev_use_range_ref)
			    = RangesOverlap($prev_used_region,$nucl_range);
			last if ($was_prev_used);
		    }
		    next if ($was_prev_used);

		    push(@HitAminoStarts,$amino_start);
		    push(@HitAminoEnds,$amino_end);
		    push(@HitNuclStarts,$nucl_start);
		    push(@HitNuclEnds,$nucl_end);
		    push(@HitEVals,$e_val);
		    $num_tbn_hits++;

		    push(@PrevUsedRegions,$nucl_range);

		}
	    }
	    close($tbnf);

	}

	# For outputting, let's get the textual representation of direction
	# into the chromosome name (after recording the chromosome length of
	# our target species, for exon overlap checking).
	my $chr_len = $ChrLensBySpecies{$target_species.'|'.$chr};
	$chr = $chr.'[revcomp]' if ($revcomp);

	# Speaking of outputting, let's just have these tidbits on-hand, too
	my $query_species = $QuerySpecies[$ghost_id];

	my $target_info = "MSA Exon Index  : Exon $MSAExons[$ghost_id]\n";
	$target_info = $target_info."    Target Genome   : $target_species ($chr:$target_start..$target_end)\n";
	$target_info = $target_info."    Query Species   : $query_species (Aminos $QueryAminoRanges[$ghost_id])\n";
	
	# Is it an especially elusive ghost we're chasing?
	if ($num_tbn_hits == 0) {
	    print $outf "[ ] Search failure (no tblastn hits)\n";
	    print $outf "    $target_info";
	    print $outf "    Query Sequence  : $QuerySeqs[$ghost_id]\n\n";
	    next;
	}
	
	# Oh, this is a most profitable Ghost Adventure indeed!
	$ghosts_busted++;

	# Let's illustrate how much of the sequence has been covered.
	# NOTE: We're assuming that our hits are consistent with one another,
	#   but we may want to double-check that in the future...
	my @MappedSeq = split(//,lc($QuerySeqs[$ghost_id]));
	for (my $hit=0; $hit<$num_tbn_hits; $hit++) {
	    for (my $pos=$HitAminoStarts[$hit]-1; $pos<$HitAminoEnds[$hit]; $pos++) {
		$MappedSeq[$pos] = uc($MappedSeq[$pos]);
	    }
	}
	my $mapped_seq = '';
	foreach my $char (@MappedSeq) {
	    $mapped_seq = $mapped_seq.$char;
	}

	# Sing it to high heaven!
	print $outf "[+] Search success!\n";
	print $outf "    $target_info";
	print $outf "    Query Sequence  : $mapped_seq\n";
	print $outf "    Num tblastn Hits: $num_tbn_hits\n";

	for (my $hit=0; $hit<$num_tbn_hits; $hit++) {

	    # What aminos (within the species sequence) were part of this hit?
	    $QueryAminoRanges[$ghost_id] =~ /(\d+)\.\./;
	    my $hit_amino_start = $HitAminoStarts[$hit];
	    my $hit_amino_end   = $hit_amino_start + ($HitAminoEnds[$hit] - $HitAminoStarts[$hit]);
	    
	    print $outf "    + Aminos $hit_amino_start..$hit_amino_end ";
	    print $outf "mapped to $target_species $chr:$HitNuclStarts[$hit]..$HitNuclEnds[$hit] ";
	    print $outf "($HitEVals[$hit])\n";

	}
	
	print $outf "\n";
	
    }

    close($outf);

    # How'd we do there?
    return ($num_ghost_exons, $ghosts_busted);

}






###############################################################
#
#  Function: FindAliQualityDrops
#
sub FindAliQualityDrops
{
    my $pcts_id_ref = shift;
    my $num_exons = shift;

    my @PctsID = @{$pcts_id_ref};

    # At what drop from a local maximum exon pair's quality
    # do we get concerned?
    my $q_drop_threshold = 25; # rec. 35+ for the alt. approach.

    # To avoid a bookkeeping headache, we'll just do two passes
    # (left-to-right, right-to-left, DUH).
    my @HasQDrop;
    for (my $i=0; $i<$num_exons; $i++) {
	$HasQDrop[$i] = 0;
    }

    my $exon_id = 0;
    while ($exon_id < scalar(@PctsID) && $PctsID[$exon_id] == 0) {
	$exon_id++;
    }
    my $last_exon_pct_id = $PctsID[$exon_id++];

    while ($exon_id < $num_exons) {
	if ($PctsID[$exon_id]) {
	    if ($last_exon_pct_id - $PctsID[$exon_id] >= $q_drop_threshold) {
		$HasQDrop[$exon_id] = 1;
	    }
	    $last_exon_pct_id = $PctsID[$exon_id];
	}
	$exon_id++;
    }

    # Reverse course!
    # Note that exon_id starts out-of-bounds, so we decrement before anything else
    while ($exon_id) {
	$exon_id--;
	if ($PctsID[$exon_id]) {
	    if ($last_exon_pct_id - $PctsID[$exon_id] >= $q_drop_threshold) {
		$HasQDrop[$exon_id] = 1;
	    }
	    $last_exon_pct_id = $PctsID[$exon_id];
	}	
    }

    # We can imagine a case where we have something like 100/50/45/50/100,
    # but if we stick with what we have now, that middle exon isn't going
    # to be seen as low-quality.
    # To remedy this, we'll run along from each low-quality exon labeling any
    # exons that don't improve by >5% as also low-quality.
    # Again, to simplify this we'll just do a left-to-right and a right-to-left
    # scan.
    while ($exon_id < $num_exons) {
	if ($HasQDrop[$exon_id]) {
	    my $pct_to_beat = $PctsID[$exon_id] + 5.0;
	    $exon_id++;
	    while ($exon_id < $num_exons) {
		if ($PctsID[$exon_id]) {
		    if ($PctsID[$exon_id] < $pct_to_beat) {
			$HasQDrop[$exon_id] = 1;
		    } else {
			last;
		    }
		}
		$exon_id++;
	    }
	} else {
	    $exon_id++;
	}
    }

    while ($exon_id > 0) {
	$exon_id--;
	if ($HasQDrop[$exon_id]) {
	    my $pct_to_beat = $PctsID[$exon_id] + 5.0;
	    $exon_id--;
	    while ($exon_id >= 0) {
		if ($PctsID[$exon_id]) {
		    if ($PctsID[$exon_id] < $pct_to_beat) {
			$HasQDrop[$exon_id] = 1;
		    } else {
			last;
		    }
		}
		$exon_id--;
	    }
	}
    }

    # Phew! So close to being done!
    # Now we just need to get a list of the QDroppers and be on
    # our merry way.
    my @LowQExonPairs;
    for (my $i=0; $i<$num_exons; $i++) {
	if ($HasQDrop[$i]) {
	    push(@LowQExonPairs,$i);
	}
    }

    if (scalar(@LowQExonPairs) == 0) {
	return 0;
    }
    return \@LowQExonPairs;





    ###########################################
    #                                         #
    #  ALT APPROACH: DROP FROM LOCAL MAXIMUM  #
    #                                         #
    ###########################################
    #
    # NOTE: An issue with this method was that we would see some
    #       extremely high-quality exon alignments (e.g., 100%),
    #       from which the alignment quality would slowly walk down
    #       to something like 68%, thus flagging that lower-scoring
    #       exon even if it were flanked by 70s-ish exons.
    #


    # We'll start off by computing the avg. pct ID (ignoring 0s)
    # and initializing an array to store 'quality ratings'
    my $avg_pct_id = 0.0;
    my $num_nonzero = 0;
    my @QualityRatings;
    foreach my $pct_id (@PctsID) {
	push(@QualityRatings,0);
	if ($pct_id) {
	    $avg_pct_id += $pct_id;
	    $num_nonzero++;
	}
    }
    
    if ($num_nonzero) {
	$avg_pct_id /= $num_nonzero;
    } else {
	return 0;
    }

    # Next up, we'll give a '1' to every exon pair that has an
    # alignment quality equal to or above the average and a '-1'
    # to every pair below the average
    my @TopShelfExons;
    for (my $i=0; $i<$num_exons; $i++) {
	if ($PctsID[$i] >= $avg_pct_id) {
	    $QualityRatings[$i] = 1;
	} elsif ($PctsID[$i]) {
	    $QualityRatings[$i] = -1;
	}
    }

    # Find the local maxima.  Note that this isn't "every peak,"
    # but rather a maximum among a set of relatively strong exons.
    my @LocalMaxima;
    for (my $i=0; $i<$num_exons; $i++) {

        if ($QualityRatings[$i] == 1) {

	    my $max_pct = $PctsID[$i];
	    my $max_pos = $i;

	    $i++;
	    while ($i<$num_exons && $QualityRatings[$i] != -1) {
		if ($PctsID[$i] > $max_pct) {
		    $max_pct = $PctsID[$i];
		    $max_pos = $i;
		}
		$i++;
	    }

	    $QualityRatings[$max_pos] = 2;
	    push(@LocalMaxima,$max_pos);
	    
	}
	
    }


    # Now we can run in both directions from each local maximum
    # checking for drops below our q-drop threshold
    foreach my $max_pos (@LocalMaxima) {

	my $pct_id_cutoff = $PctsID[$max_pos] - $q_drop_threshold;

	# Scan left
	for (my $i=$max_pos-1; $i>=0; $i--) {
	    last if ($QualityRatings[$i] == 2);
	    if ($PctsID[$i] && $PctsID[$i] <= $pct_id_cutoff) {
		$QualityRatings[$i] = -2;
	    }
	}
	
	# Scan right
	for (my $i=$max_pos+1; $i<$num_exons; $i++) {
	    last if ($QualityRatings[$i] == 2);
	    if ($PctsID[$i] && $PctsID[$i] <= $pct_id_cutoff) {
		$QualityRatings[$i] = -2;
	    }
	}
	
    }

    # Finally, we can condense our below-threshold exons into a list
    my @QDroppers;
    for (my $i=0; $i<$num_exons; $i++) {
	push(@QDroppers,$i) if ($QualityRatings[$i] == -2);
    }

    return \@QDroppers;
    
}






###############################################################
#
#  Function:  RecordGhostMSAs
#
sub RecordGhostMSAs
{
    my $gene = shift;

    # First things first, we're going to need to grab ahold of this gene's dir
    my $genedir = ConfirmDirectory($outgenesdir.$gene);

    # Open up the file with all of the hits for this gene and read in all
    # successful maps
    my $SearchFile = OpenInputFile($genedir.'search.out');

    my %TargetSpeciesToHitIDs;
    my @AllGeneHits;
    my $num_gene_hits = 0;
    while (my $line = <$SearchFile>) {

	next if ($line !~ /\[\+\] Search success/);

	
	$line = <$SearchFile>;
	$line =~ /\: Exon (\d+)/;

	my $exon_id = $1;

	
	$line = <$SearchFile>;
	$line =~ /\: (\S+)/;

	my $target_species = $1;


	$line = <$SearchFile>;
	$line =~ /\: (\S+) \(Aminos (\S+)\)/;

	my $query_species = $1;
	my $query_range = $2;


	$line = <$SearchFile>;
	$line =~ /\: (\S+)/;

	my $query_seq = $1;


	$line = <$SearchFile>;
	$line =~ /Num tblastn Hits\: (\d+)/;

	my $num_tblastn_hits = $1;
	for (my $tblastn_hit=0; $tblastn_hit<$num_tblastn_hits; $tblastn_hit++) {

	    $line = <$SearchFile>;
	    $line =~ /mapped to $target_species (\S+)/;

	    my $target_range = $1;

	    
	    my $hit_data = $exon_id.'|'.$target_range.'|'.$query_species.':'.$query_range.'|'.$query_seq;

	    $AllGeneHits[++$num_gene_hits] = $hit_data;

	    if ($TargetSpeciesToHitIDs{$target_species}) {
		$TargetSpeciesToHitIDs{$target_species} = $TargetSpeciesToHitIDs{$target_species}.','.$num_gene_hits;
	    } else {
		$TargetSpeciesToHitIDs{$target_species} = $num_gene_hits;
	    }

	}
	
    }

    return if ($num_gene_hits == 0);

    my $gene_alis_dir_name = CreateDirectory($genedir.'alignments');

    foreach my $target_species (sort keys %TargetSpeciesToHitIDs) {

	my %ExonToHitIDs;
	foreach my $hit_id (split(/\,/,$TargetSpeciesToHitIDs{$target_species})) {

	    $AllGeneHits[$hit_id] =~ /^([^\|]+)\|/;
	    my $exon = $1;

	    if ($ExonToHitIDs{$exon}) {
		$ExonToHitIDs{$exon} = $ExonToHitIDs{$exon}.','.$hit_id;
	    } else {
		$ExonToHitIDs{$exon} = $hit_id;
	    }
	}


	my $species_out_file_name = $gene_alis_dir_name.$target_species.'.'.$gene.'.out';
	my $SpeciesOutFile = OpenOutputFile($species_out_file_name);
	my $num_species_outputs = 0;

	foreach my $exon (sort {$a <=> $b} keys %ExonToHitIDs) {

	    my @ExonTargetChrs;
	    my @ExonTargetRanges;
	    my @ExonQuerySpecies;
	    my @ExonQueryRanges;
	    my @ExonQuerySeqs;
	    my $num_exon_hits = 0;
	    foreach my $hit_id (split(/\,/,$ExonToHitIDs{$exon})) {

		my @HitData = split(/\|/,$AllGeneHits[$hit_id]);

		$HitData[1] =~ /^([^\:]+)\:(\S+)$/;
		push(@ExonTargetChrs,$1);
		push(@ExonTargetRanges,$2);

		$HitData[2] =~ /^([^\:]+)\:(\S+)$/;
		push(@ExonQuerySpecies,$1);
		push(@ExonQueryRanges,$2);

		push(@ExonQuerySeqs,$HitData[3]);

		$num_exon_hits++;
		
	    }

	    my %AlreadyRecordedTargetChrs;
	    for (my $exon_hit_id = 0; $exon_hit_id < $num_exon_hits; $exon_hit_id++) {

		my $target_chr = $ExonTargetChrs[$exon_hit_id];
		
		# Have we already taken care of hits to this chromosome?
		next if ($AlreadyRecordedTargetChrs{$target_chr});

		# Well, it's time for this chromosome, then!
		my @ChrGroupTargetRanges;
		my @ChrGroupQuerySpecies;
		my @ChrGroupQueryRanges;
		my @ChrGroupQuerySeqs;
		my $num_chr_group_hits = 0;
		for (my $check_id=$exon_hit_id; $check_id < $num_exon_hits; $check_id++) {

		    if ($ExonTargetChrs[$check_id] eq $target_chr) {

			push(@ChrGroupTargetRanges,$ExonTargetRanges[$check_id]);
			push(@ChrGroupQuerySpecies,$ExonQuerySpecies[$check_id]);
			push(@ChrGroupQueryRanges,$ExonQueryRanges[$check_id]);
			push(@ChrGroupQuerySeqs,$ExonQuerySeqs[$check_id]);

			$num_chr_group_hits++;
			
		    }
		    
		}

		
		# Now that we have all of the hits that landed on this chromosome,
		# the very last thing we need to do identify the overlapping regions
		my @OverlapGroups;
		my @OverlapGroupToRange;
		my $num_overlap_groups = 0;
		for (my $i=0; $i<$num_chr_group_hits; $i++) {
		    $OverlapGroups[$i] = 0;
		}

		while (1) {

		    my $base_hit_id = 0;
		    while ($base_hit_id < $num_chr_group_hits && $OverlapGroups[$base_hit_id]) {
			$base_hit_id++;
		    }

		    # If we walked all the way up to our count, we're fully grouped!
		    last if ($base_hit_id == $num_chr_group_hits);

		    # Build up a grouping of all hits that overlap with
		    # hits that overlap with ChrGroupTargetRanges[base_hit_id]
		    my $overlap_range = $ChrGroupTargetRanges[$base_hit_id];

		    while (1) {

			my $range_record = $overlap_range;

			for (my $i=0; $i<$num_chr_group_hits; $i++) {

			    # If this hit is already grouped, skip it
			    next if ($OverlapGroups[$i]);

			    my ($overlap_check, $check_overlap_range)
				= RangesOverlap($ChrGroupTargetRanges[$i],$overlap_range);

			    $overlap_range = $check_overlap_range if ($overlap_check);
			    
			}

			# If the last scan didn't change our range, we're done!
			last if ($range_record eq $overlap_range);
			
		    }

		    # Record which hits the new overlap range covers
		    $num_overlap_groups++;
		    $OverlapGroupToRange[$num_overlap_groups] = $overlap_range;
		    for (my $i=0; $i<$num_chr_group_hits; $i++) {
			next if ($OverlapGroups[$i]);
			my ($overlap_check, $check_overlap_range)
			    = RangesOverlap($ChrGroupTargetRanges[$i],$overlap_range);
			$OverlapGroups[$i] = $num_overlap_groups if ($overlap_check);
		    }
		    
		}

		
		# Iterate over all groups of hits that overlap (in terms of their
		# positions on the target chromosome) and generate an alignment for
		# each group
		for (my $hit_group_id = 1; $hit_group_id <= $num_overlap_groups; $hit_group_id++) {
		    
		    my @GroupQuerySpecies;
		    my @GroupQueryRanges;
		    my @GroupQuerySeqs;

		    for (my $i=0; $i<$num_chr_group_hits; $i++) {
			if ($OverlapGroups[$i] == $hit_group_id) {
			    push(@GroupQuerySpecies,$ChrGroupQuerySpecies[$i]);
			    push(@GroupQueryRanges,$ChrGroupQueryRanges[$i]);
			    push(@GroupQuerySeqs,$ChrGroupQuerySeqs[$i]);
			}
		    }

		    my $frame_out_strs_ref = GenMultiAliString($genedir,$exon,$target_species,$target_chr,
							       $OverlapGroupToRange[$hit_group_id],
							       \@GroupQuerySpecies,\@GroupQueryRanges,\@GroupQuerySeqs);

		    my @FrameOutStrs = @{$frame_out_strs_ref};

		    foreach my $frame_out_str (@FrameOutStrs) {
			$num_species_outputs++;
			next if (!$frame_out_str);
			print $SpeciesOutFile "$frame_out_str";
			print $SpeciesOutFile "\n  ==========================================\n\n";
		    }
		    
		}

		
		# Done!
		$AlreadyRecordedTargetChrs{$target_chr} = 1;
		
	    }
	    
	}

	close($SpeciesOutFile);
	RunSystemCommand("rm \"$species_out_file_name\"") if ($num_species_outputs == 0);
	
    }

}





###############################################################
#
#  Function:  GenMultiAliString
#
sub GenMultiAliString
{
    my $genedir = shift;
    
    my $exon_id = shift;
    
    my $target_species = shift;
    my $target_chr = shift;
    my $target_range = shift;

    my $query_species_ref = shift;
    my $query_amino_ranges_ref = shift;
    my $query_amino_seqs_ref = shift;

    my @QuerySpecies = @{$query_species_ref};
    my @QueryAminoRanges = @{$query_amino_ranges_ref};
    my @QueryAminoSeqs = @{$query_amino_seqs_ref};

    my $num_queries = scalar(@QueryAminoSeqs);

    # How many nucleotides do we want on either side of the
    # alignment visualization?  (default is 60 because that
    # gives us a full line before the alignment starts)
    my $nucl_buffer_len = 60;

    $target_range =~ /^(\d+)\.\.(\d+)$/;
    my $target_start = $1;
    my $target_end = $2;

    my $revcomp = 0;
    my $search_target_chr = $target_chr;
    my $extra_search_nucls = 100;
    if ($target_chr =~ /\[revcomp\]/) {
	$search_target_chr =~ s/\[revcomp\]//;
	$revcomp = 1;
	$target_start += $extra_search_nucls + $nucl_buffer_len;
	$target_end   -= $extra_search_nucls + $nucl_buffer_len;
    } else {
	$target_start -= $extra_search_nucls + $nucl_buffer_len;
	$target_end   += $extra_search_nucls + $nucl_buffer_len;
    }

    
    my $sfetch_cmd = $sfetch.' -range '.$target_start.'..'.$target_end;
    $sfetch_cmd = $sfetch_cmd.' '.$SpeciesToGenomes{$target_species}.' '.$search_target_chr;

    my $NuclFile = OpenSystemCommand($sfetch_cmd);
    <$NuclFile>;
    my $nucl_seq = '';
    while (my $line = <$NuclFile>) {
	$line =~ s/\n|\r//g;
	$nucl_seq = $nucl_seq.$line;
    }
    close($NuclFile);
    my @Nucls = split(//,uc($nucl_seq));

    # In order to guarantee that we don't eat into our designated
    # buffer we limit the search area to not include the
    # 'nucl_buffer_len' nucleotides on either side of the full
    # chunk of genomic sequence that we pulled
    my @SearchNucls;
    for (my $i=$nucl_buffer_len; $i<scalar(@Nucls)-$nucl_buffer_len; $i++) {
	push(@SearchNucls,$Nucls[$i]);
    }
    
    my @TransFrames;
    for (my $frame=0; $frame<3; $frame++) {

	my $frame_str = '';
	for (my $codon_start = $frame; $codon_start+2 < scalar(@SearchNucls); $codon_start += 3) {
	    my $amino = TranslateCodon($SearchNucls[$codon_start].$SearchNucls[$codon_start+1].$SearchNucls[$codon_start+2]);
	    $frame_str = $frame_str.$amino;
	}

	$TransFrames[$frame] = uc($frame_str);
	
    }


    my @AliReadingFrames;
    my @AliTargetRanges;
    my @AliQueryRanges;
    
    for (my $query_id = 0; $query_id < $num_queries; $query_id++) {

	my $best_ali_score        = -1;
	my $best_ali_frame        = -1;
	my $best_ali_target_range = -1;
	my $best_ali_query_range  = -1;

	for (my $frame = 0; $frame < 3; $frame++) {

	    my ($frame_num_alis,$frame_ali_score_densities_ref,$frame_ali_scores_ref,
		$frame_ali_target_ranges_ref,$frame_ali_query_ranges_ref)
		= GatherBestLocalAlis($TransFrames[$frame],0,$QueryAminoSeqs[$query_id],0);
	    next if (!$frame_num_alis);

	    
	    my @FrameAliScores = @{$frame_ali_scores_ref};
	    my @FrameAliTargetRanges = @{$frame_ali_target_ranges_ref};
	    my @FrameAliQueryRanges = @{$frame_ali_query_ranges_ref};

	    for (my $i=0; $i<$frame_num_alis; $i++) {

		if ($FrameAliScores[$i] > $best_ali_score) {

		    $best_ali_score = $FrameAliScores[$i];
		    $best_ali_frame = $frame;
		    $best_ali_target_range = $FrameAliTargetRanges[$i];
		    $best_ali_query_range = $FrameAliQueryRanges[$i];
		    
		}
		
	    }
	    
	}

	$AliReadingFrames[$query_id] = $best_ali_frame;
	$AliTargetRanges[$query_id] = $best_ali_target_range;
	$AliQueryRanges[$query_id] = $best_ali_query_range;
				      
    }


    # Even though it's probably a little bit silly, we'll run through
    # each reading frame and generate a frame-specific alignment
    # (this should almost always be just one frame, but never hurts
    # to be able to catch dual-coding stuff!)
    my @FrameOutStrs;
    for (my $frame=0; $frame<3; $frame++) {

	$FrameOutStrs[$frame] = '';
	
	# Which queries used this reading frame?
	my @FrameUsers;
	my @FrameQuerySeqs;
	my $num_frame_users = 0;

	# What parts of the target did they align to?
	# NOTE that these are amino acid coordinates within
	# the translated string.
	my $frame_target_start = 0;
	my $frame_target_end   = 0;
	for (my $query_id=0; $query_id<$num_queries; $query_id++) {
	    if ($AliReadingFrames[$query_id] == $frame) {

		push(@FrameUsers,$query_id);
		$num_frame_users++;

		# Grab the portion of this query that aligns well
		# to our target
		$AliQueryRanges[$query_id] =~ /^(\d+)\.\.(\d+)/;
		my $ali_query_start = $1;
		my $ali_query_end   = $2;

		my @QuerySeq = split(//,$QueryAminoSeqs[$query_id]);
		my $frame_query_seq = '';
		for (my $i=$ali_query_start; $i<=$ali_query_end; $i++) {
		    $frame_query_seq = $frame_query_seq.uc($QuerySeq[$i]);
		}
		push(@FrameQuerySeqs,$frame_query_seq);

		# Make sure we're keeping hold of the portion of the
		# target (translated) sequence that our queries like
		# to align to.
		$AliTargetRanges[$query_id] =~ /^(\d+)\.\.(\d+)$/;
		my $ali_target_start = $1;
		my $ali_target_end   = $2;

		if (!$frame_target_start) {
		    $frame_target_start = $ali_target_start;
		    $frame_target_end   = $ali_target_end;
		} else {
		    $frame_target_start = Min($frame_target_start,$ali_target_start);
		    $frame_target_end   = Max($frame_target_end  ,$ali_target_end  );
		}

	    }
	}

	
	# If none of the queries used this reading frame, skip it!
	next if ($num_frame_users == 0);

	
	# Tight! Let's align them query sequences to our target sequence!
	my @TransFrameChars = split(//,$TransFrames[$frame]);
	my @AminoAlignment;
	for (my $i=$frame_target_start; $i<=$frame_target_end; $i++) {
	    push(@AminoAlignment,$TransFrameChars[$i]);
	}
	for (my $i=0; $i<$num_frame_users; $i++) {
	    my @QueryAminos   = split(//,$FrameQuerySeqs[$i]);
	    my $amino_ali_ref = MultiAminoSeqAli(\@AminoAlignment,\@QueryAminos);
	    @AminoAlignment   = @{$amino_ali_ref};
	}
	my $amino_ali_length = scalar(@AminoAlignment);


	my $ali_nucl_start_index = 3 * $frame_target_start + $frame;
	my $ali_nucl_end_index   = 3 * $frame_target_end   + $frame + 2;


	my @AliNucls;
	for (my $i=$ali_nucl_start_index; $i<=$ali_nucl_end_index; $i++) {
	    push(@AliNucls,$SearchNucls[$i]);
	}

	
	# What are the actual nucleotide coordinates of our alignment?
	my $ali_nucl_start = $target_start;
	my $ali_nucl_end = $ali_nucl_start;
	if ($revcomp) {
	    $ali_nucl_start -= $ali_nucl_start_index + $nucl_buffer_len;
	    $ali_nucl_end   -= $ali_nucl_end_index   + $nucl_buffer_len;
	} else {
	    $ali_nucl_start += $ali_nucl_start_index + $nucl_buffer_len;
	    $ali_nucl_end   += $ali_nucl_end_index   + $nucl_buffer_len;
	}

	
	# The very last thing we'll do before starting work
	# on the visualization matrix is to pull in 60 nucleotides
	# on either side of the alignment region.
	#
	# MATH NOTE: Because the position should shift over
	#   nucl_buffer_len nucleotides to switch indices from
	#   SearchNucls to Nucls, our left buffer starts at
	#   'ali_nucl_start_index'
	#
	my @LeftNuclBuffer;
	for (my $i=$ali_nucl_start_index; $i<$ali_nucl_start_index+$nucl_buffer_len; $i++) {
	    push(@LeftNuclBuffer,lc($Nucls[$i]));
	}

	my @RightNuclBuffer;
	for (my $i=$ali_nucl_end_index+$nucl_buffer_len+1; $i<=$ali_nucl_end_index+(2*$nucl_buffer_len); $i++) {
	    push(@RightNuclBuffer,lc($Nucls[$i]));
	}

	
	# Now we can start building up our visualization matrix!
	my @VisMatrix;

	# We'll start by incorporating the left-side nucleotide buffer
	my $vis_matrix_len = 0;
	for (my $i=0; $i<$nucl_buffer_len; $i++) {

	    $VisMatrix[0][$vis_matrix_len] = ' ';
	    $VisMatrix[1][$vis_matrix_len] = $LeftNuclBuffer[$i];
	    for (my $j=0; $j<$num_frame_users; $j++) {
		$VisMatrix[2+$j][$vis_matrix_len] = ' ';
	    }
	    $vis_matrix_len++;

	}


	# Now we can build up the body of the visualization matrix
	# (and, simultaneously, our match / mismatch counts for each source)
	my @QueryAliMatches;
	my @QueryAliMismatches;
	for (my $i=0; $i<$num_frame_users; $i++) {
	    $QueryAliMatches[$i] = 0;
	    $QueryAliMismatches[$i] = 0;
	}
	
	my $nucl_chars_pos = 0;
	for (my $i=0; $i<$amino_ali_length; $i++) {

	    my @AminoColumn = split(//,$AminoAlignment[$i]);

	    my $insertion = 0;
	    $insertion = 1 if ($AminoColumn[0] eq '-');
	    
	    # Left nucleotide of codon
	    # = Translation
	    $VisMatrix[0][$vis_matrix_len] = ' ';
	    # = Nucleotides
	    if ($insertion) { $VisMatrix[1][$vis_matrix_len] = '-';                          }
	    else            { $VisMatrix[1][$vis_matrix_len] = $AliNucls[$nucl_chars_pos++]; }
	    # = Queries
	    for (my $j=0; $j<$num_frame_users; $j++) {
		$VisMatrix[2+$j][$vis_matrix_len] = ' ';
	    }
	    $vis_matrix_len++;

	    # Center nucleotide (and aminos!)
	    # = Translation
	    $VisMatrix[0][$vis_matrix_len] = $AminoColumn[0];
	    # = Nucleotides
	    if ($insertion) { $VisMatrix[1][$vis_matrix_len] = '-';                          }
	    else            { $VisMatrix[1][$vis_matrix_len] = $AliNucls[$nucl_chars_pos++]; }
	    # = Queries
	    for (my $j=0; $j<$num_frame_users; $j++) {
		
		my $query_ali_amino = $AminoColumn[$j+1];
		if ($insertion) {
		    if ($query_ali_amino =~ /[A-Z]/) {
			$VisMatrix[2+$j][$vis_matrix_len] = lc($query_ali_amino);
			$QueryAliMismatches[$j]++;
		    } else {
			$VisMatrix[2+$j][$vis_matrix_len] = '-';
		    }
		    next;
		}

		if ($query_ali_amino =~ /[A-Z]/) {
		    if ($query_ali_amino eq $AminoColumn[0]) {
			$VisMatrix[2+$j][$vis_matrix_len] = '.';
			$QueryAliMatches[$j]++;
		    } else {
			$VisMatrix[2+$j][$vis_matrix_len] = lc($query_ali_amino);
			$QueryAliMismatches[$j]++;
		    }
		} else {
		    $VisMatrix[2+$j][$vis_matrix_len] = $query_ali_amino; # Presumably '-'
		    $QueryAliMismatches[$j]++;
		}

	    }
	    $vis_matrix_len++;

	    # Right nucleotide of codon
	    # = Translation
	    $VisMatrix[0][$vis_matrix_len] = ' ';
	    # = Nucleotides
	    if ($insertion) { $VisMatrix[1][$vis_matrix_len] = '-';                          }
	    else            { $VisMatrix[1][$vis_matrix_len] = $AliNucls[$nucl_chars_pos++]; }
	    # = Queries
	    for (my $j=0; $j<$num_frame_users; $j++) {
		$VisMatrix[2+$j][$vis_matrix_len] = ' ';
	    }
	    $vis_matrix_len++;


	}

	# Finally, we'll wrap up with the right-side nucleotide buffer
	for (my $i=0; $i<$nucl_buffer_len; $i++) {

	    $VisMatrix[0][$vis_matrix_len] = ' ';
	    $VisMatrix[1][$vis_matrix_len] = $RightNuclBuffer[$i];
	    for (my $j=0; $j<$num_frame_users; $j++) {
		$VisMatrix[2+$j][$vis_matrix_len] = ' ';
	    }
	    $vis_matrix_len++;
	    
	}


	# Mainly for aesthetics (although this also makes percents ID a bit
	# more true-to-presentation) we'll trim off any leading or trailing
	# gaps from our queries in the alignment
	for (my $i=0; $i<$num_frame_users; $i++) {

	    my $ali_row = $i+2;

	    my $ali_col = 0;
	    while ($ali_col < $vis_matrix_len && $VisMatrix[$ali_row][$ali_col] !~ /\.|[a-z]/) {
		if ($VisMatrix[$ali_row][$ali_col] eq '-' && $VisMatrix[0][$ali_col] =~ /[A-Z]/) {
		    $VisMatrix[$ali_row][$ali_col] = ' ';
		    $QueryAliMismatches[$i]--;
		}
		$ali_col++;
	    }

	    $ali_col = $vis_matrix_len-1;
	    while ($ali_col >= 0 && $VisMatrix[$ali_row][$ali_col] !~ /\.|[a-z]/) {
		if ($VisMatrix[$ali_row][$ali_col] eq '-' && $VisMatrix[0][$ali_col] =~ /[A-Z]/) {
		    $VisMatrix[$ali_row][$ali_col] = ' ';
		    $QueryAliMismatches[$i]--;
		}
		$ali_col--;
	    }
	    
	}


	# Great work!  That covers the main visualization of the alignment,
	# but we also want to make sure that each row is given a label
	my @VisMatrixRowLabels;
	$VisMatrixRowLabels[0] = $target_species;
	$VisMatrixRowLabels[1] = '';
	my $longest_row_label_length = length($target_species);
	for (my $i=0; $i<$num_frame_users; $i++) {

	    my $query_id = $FrameUsers[$i];
	    my $query_species = $QuerySpecies[$query_id];
	    
	    $VisMatrixRowLabels[2+$i] = $query_species;
	    if (length($query_species) > $longest_row_label_length) {
		$longest_row_label_length = length($query_species);
	    }
	    
	}

	for (my $i=0; $i<$num_frame_users+2; $i++) {
	    while (length($VisMatrixRowLabels[$i]) < $longest_row_label_length) {
		$VisMatrixRowLabels[$i] = ' '.$VisMatrixRowLabels[$i];
	    }
	}


	# YEE-HAW! Time to figure out all the deets for our final reporting!
	my $gtf_overlap_str = "Novel exon (no GTF overlaps)";
	if (IsGTFAnnotated($target_species,$search_target_chr,$ali_nucl_start,$ali_nucl_end)) {
	    $gtf_overlap_str = "Overlaps with GTF entry";
	}
	
	my $metadata_str = "\n  Target : $target_species $target_chr:$ali_nucl_start..$ali_nucl_end\n";
	$metadata_str    = $metadata_str."         : $gtf_overlap_str\n";
	$metadata_str    = $metadata_str."  Query  : Exon $exon_id (Species-wise MSA)\n";

	for (my $i=0; $i<$num_frame_users; $i++) {

	    my $query_id = $FrameUsers[$i];
	    my $query_species = $QuerySpecies[$query_id];

	    $AliQueryRanges[$query_id] =~ /^(\d+)\.\.(\d+)$/;
	    my $query_ali_start = $1;
	    my $query_ali_end   = $2;
	    
	    $QueryAminoRanges[$query_id] =~ /^(\d+)\.\./;
	    my $query_start_amino = $1;

	    $query_ali_start += $query_start_amino;
	    $query_ali_end   += $query_start_amino;

	    my $query_matches = $QueryAliMatches[$i];
	    my $total_query_cols = $QueryAliMatches[$i] + $QueryAliMismatches[$i];
	    my $query_ali_pct_id = int(1000.0 * $query_matches / $total_query_cols) / 10.0;

	    my $query_lift_str = GenQueryLiftString($genedir,$query_species,$query_ali_start,$query_ali_end);

	    $metadata_str = $metadata_str."         : $query_species / ";
	    $metadata_str = $metadata_str."aminos $query_ali_start..$query_ali_end ($query_lift_str) / ";
	    $metadata_str = $metadata_str."$query_ali_pct_id% alignment identity\n";
	    
	}
	$metadata_str = $metadata_str."\n";
	

	# Put together the alignment string
	my $ali_vis_str = "\n";
	my $ali_vis_col = 0;
	my $line_length = 60;
	while ($ali_vis_col < $vis_matrix_len) {

	    my $line_break_col = Min($ali_vis_col+$line_length, $vis_matrix_len);
	    for (my $i=0; $i<$num_frame_users+2; $i++) {
		$ali_vis_str = $ali_vis_str.$VisMatrixRowLabels[$i].'  ';
		for (my $j=$ali_vis_col; $j<$line_break_col; $j++) {
		    $ali_vis_str = $ali_vis_str.$VisMatrix[$i][$j];
		}
		$ali_vis_str = $ali_vis_str."\n";
	    }
	    $ali_vis_str = $ali_vis_str."\n\n";

	    $ali_vis_col = $line_break_col;
	    
	}

	$FrameOutStrs[$frame] = $metadata_str.$ali_vis_str;
	
    }

    return \@FrameOutStrs;
    
}





###############################################################
#
#  Function:  GenQueryLiftString
#
sub GenQueryLiftString
{

    my $genedir = shift;
    my $query_species = shift;
    my $query_start = shift;
    my $query_end = shift;
    
    # Let's go out to the genome mappings for each of our source species
    # and figure out what coordinates on their genomes correspond to the
    # exon that we found (lifty-overy-stuffy)
    my $MapCoordFile = OpenInputFile($genedir.'genome-mappings.out');
    my $lift_str = '';
    while (my $line = <$MapCoordFile>) {
	
	next if ($line !~ /Species\s+\:\s+(\S+)/);
	my $species = $1;
	next if ($species ne $query_species);

	# Great!  Let's grab some coord.s!
	$line = <$MapCoordFile>;
	$line =~ /Chromosome\s+\:\s+(\S+)/;
	my $query_chr = $1;

	my $revcomp = 0;
	$revcomp = 1 if ($revcomp =~ /\[revcomp\]/);
	
	$line = <$MapCoordFile>;
	$line =~ /Num Exons\s+\:\s+(\d+)/;
	
	my $num_exons = $1;
	
	for (my $exon_id=0; $exon_id<$num_exons; $exon_id++) {
	    
	    my $exon_metadata  = <$MapCoordFile>;
	    my $coord_list_str = <$MapCoordFile>;
	    
	    $exon_metadata =~ /Aminos (\d+)\.\.(\d+)\, \S+\:(\d+)\.\.(\d+)\s*$/;
	    my $exon_start_amino = $1;
	    my $exon_end_amino   = $2;
	    my $exon_start_nucl  = $3;
	    my $exon_end_nucl    = $4;
	    
	    
	    # Are we even in the right ballpark?
	    next if ($exon_end_amino < $query_start);
	    

	    # Oh, we're in the right ballpark, baby!
	    $coord_list_str =~ s/\n|\r//g;
	    my @ExonNuclCoords = split(/\,/,$coord_list_str);
	    
	    
	    # Start with the start
	    if ($exon_start_amino >= $query_start) {
		
		$lift_str = $lift_str.'/'.$exon_start_nucl;
		
	    } else {
		
		my $nucl_coord = $ExonNuclCoords[$query_start - $exon_start_amino];
		
		if ($revcomp) { $nucl_coord++; }
		else          { $nucl_coord--; }
		
		$lift_str = $lift_str.'/'.$nucl_coord;
		
	    }
	    
	    
	    # End with the end
	    if ($exon_end_amino <= $query_end) {
		
		$lift_str = $lift_str.'..'.$exon_end_nucl;
		
	    } else {
		
		my $nucl_coord = $ExonNuclCoords[$query_end - $exon_start_amino];
		
		if ($revcomp) { $nucl_coord--; }
		else          { $nucl_coord++; }
		
		$lift_str = $lift_str.'..'.$nucl_coord;
		
	    }
	    

	    # Have we finished the job?
	    last if ($exon_end_amino >= $query_end);
	    
	}
	
	$lift_str =~ s/^\//$query_chr\:/;
	
    }
    close($MapCoordFile);

    return $lift_str;
    
}






###############################################################
#
#  Function:  GatherBestLocalAlis
#
#  This is a recursive function used to find as many local alignments between
#  a given target and source as possible.
#
#  We find the best local alignment between the full target and source, and then
#  search the upper-left (defined by the start of the local alignment) and the
#  bottom-right (defined by the end of the local alignment) for their best
#  local alignments, going until the density of the best alignment drops below a
#  threshold or we don't have sufficient space to expect to find a good alignment.
#
sub GatherBestLocalAlis
{
    my $target_seq   = shift;
    my $target_start = shift;

    my $source_seq   = shift;
    my $source_start = shift;
    
    my @TargetChars = split(//,$target_seq);
    my @SourceChars = split(//,$source_seq);
    
    my $num_target_chars = scalar(@TargetChars);
    my $num_source_chars = scalar(@SourceChars);
    

    my ($score_density,$score,$target_ali_start,$target_ali_end,$source_ali_start,$source_ali_end)
	= LocalAlign(\@TargetChars,\@SourceChars);


    # Did we not find anything we're excited about?
    return (0,0,0,0,0) if ($score_density < $score_density_threshold);

    
    my $true_target_ali_start = $target_ali_start + $target_start;
    my $true_target_ali_end   = $target_ali_end   + $target_start;
    
    my $true_source_ali_start = $source_ali_start + $source_start;
    my $true_source_ali_end   = $source_ali_end   + $source_start;

    
    my $target_ali_range = $true_target_ali_start.'..'.$true_target_ali_end;
    my $source_ali_range = $true_source_ali_start.'..'.$true_source_ali_end;


    my $num_alis = 1;
    my @Scores;
    my @ScoreDensities;
    my @TargetRanges;
    my @SourceRanges;

    push(@Scores,$score);
    push(@ScoreDensities,$score_density);
    push(@TargetRanges,$target_ali_range);
    push(@SourceRanges,$source_ali_range);


    # Now we see what's good to the left and right of *this* optimal local alignment
    my $min_ali_len = 8;


    my @LeftScores;
    my @LeftDensities;
    my @LeftTargetRanges;
    my @LeftSourceRanges;
    if (Min($target_ali_start,$source_ali_start) > $min_ali_len) {

	my @LeftTargetChars;
	for (my $i=0; $i<$target_ali_start; $i++) {
	    push(@LeftTargetChars,$TargetChars[$i]);
	}

	my @LeftSourceChars;
	for (my $j=0; $j<$source_ali_start; $j++) {
	    push(@LeftSourceChars,$SourceChars[$j]);
	}
	
	my ($num_left_alis,$left_dens_ref,$left_scores_ref,$left_target_ranges_ref,$left_source_ranges_ref)
	    = GatherBestLocalAlis(\@LeftTargetChars,$target_start,
				  \@LeftSourceChars,$source_start);

	if ($num_left_alis) {
	    @LeftScores = @{$left_scores_ref};
	    @LeftDensities = @{$left_dens_ref};
	    @LeftTargetRanges = @{$left_target_ranges_ref};
	    @LeftSourceRanges = @{$left_source_ranges_ref};
	}
	
    }


    my @RightScores;
    my @RightDensities;
    my @RightTargetRanges;
    my @RightSourceRanges;
    if (Min($num_target_chars-$target_ali_end,$num_source_chars-$source_ali_end)-1 > $min_ali_len) {

	my @RightTargetChars;
	for (my $i=$target_ali_end+1; $i<$num_target_chars; $i++) {
	    push(@RightTargetChars,$TargetChars[$i]);
	}

	my @RightSourceChars;
	for (my $j=$source_ali_end+1; $j<$num_source_chars; $j++) {
	    push(@RightSourceChars,$SourceChars[$j]);
	}
	
	my ($num_right_alis,$right_dens_ref,$right_scores_ref,$right_target_ranges_ref,$right_source_ranges_ref)
	    = GatherBestLocalAlis(\@RightTargetChars,$true_target_ali_end+1,
				  \@RightSourceChars,$true_source_ali_end+1);

	if ($num_right_alis) {
	    @RightScores = @{$right_scores_ref};
	    @RightDensities = @{$right_dens_ref};
	    @RightTargetRanges = @{$right_target_ranges_ref};
	    @RightSourceRanges = @{$right_source_ranges_ref};
	}
	
    }

    
    # Merge 'em!
    my $left_index = 0;
    my $right_index = 0;
    while ($left_index < scalar(@LeftDensities) && $right_index < scalar(@RightDensities)) {
	
	if ($LeftDensities[$left_index] > $RightDensities[$right_index]) {

	    $Scores[$num_alis] = $LeftScores[$left_index];
	    $ScoreDensities[$num_alis] = $LeftDensities[$left_index];
	    $TargetRanges[$num_alis] = $LeftTargetRanges[$left_index];
	    $SourceRanges[$num_alis] = $LeftSourceRanges[$left_index];

	    $num_alis++;
	    $left_index++;
	    
	} else {

	    $Scores[$num_alis] = $RightScores[$right_index];
	    $ScoreDensities[$num_alis] = $RightDensities[$right_index];
	    $TargetRanges[$num_alis] = $RightTargetRanges[$right_index];
	    $SourceRanges[$num_alis] = $RightSourceRanges[$right_index];

	    $num_alis++;
	    $right_index++;

	}
	
    }

    while ($left_index < scalar(@LeftDensities)) {

	$Scores[$num_alis] = $LeftScores[$left_index];
	$ScoreDensities[$num_alis] = $LeftDensities[$left_index];
	$TargetRanges[$num_alis] = $LeftTargetRanges[$left_index];
	$SourceRanges[$num_alis] = $LeftSourceRanges[$left_index];
	
	$num_alis++;
	$left_index++;
	    
    }

    while ($right_index < scalar(@RightDensities)) {

	$Scores[$num_alis] = $Scores[$right_index];
	$ScoreDensities[$num_alis] = $RightDensities[$right_index];
	$TargetRanges[$num_alis] = $RightTargetRanges[$right_index];
	$SourceRanges[$num_alis] = $RightSourceRanges[$right_index];
	
	$num_alis++;
	$right_index++;

    }

    return ($num_alis,\@ScoreDensities,\@Scores,\@TargetRanges,\@SourceRanges);
    
}
    




###############################################################
#
#  Function:  LocalAlign
#
sub LocalAlign
{

    my $seq1_ref = shift;
    my $seq2_ref = shift;

    # NOTE: As used in 'GatherBestLocalAlis' the target (translated) sequences
    #       is passed in as Seq1 and the source sequence is passed in as Seq2.

    my @Seq1 = @{$seq1_ref};
    my $len1 = scalar(@Seq1);

    my @Seq2 = @{$seq2_ref};
    my $len2 = scalar(@Seq2);

    my @Matrix;
    for (my $i=0; $i<=$len1; $i++) { $Matrix[$i][0] = 0; }
    for (my $j=0; $j<=$len2; $j++) { $Matrix[0][$j] = 0; }

    # Fill in the matrix
    my $max_i;
    my $max_j;
    my $max_score = 0;
    for (my $i=0; $i<$len1; $i++) {
	for (my $j=0; $j<$len2; $j++) {

	    # Stop codon check (we'll do both Seq1 and Seq2 -- why not?)
	    if ($Seq1[$i] eq '*' || $Seq2[$j] eq '*') {
		$Matrix[$i+1][$j+1] = 0;
		next;
	    }

	    my $match_score = GetB62Score($Seq1[$i],$Seq2[$j]) + $Matrix[$i][$j];

	    $Matrix[$i+1][$j+1] = Max(Max($Matrix[$i+1][$j],$Matrix[$i][$j+1])+$b62_gap,
				      $match_score);

	    $Matrix[$i+1][$j+1] = 0 if ($Matrix[$i+1][$j+1] < 0);

	    if ($max_score < $Matrix[$i+1][$j+1]) {
		$max_score = $Matrix[$i+1][$j+1];
		$max_i = $i+1;
		$max_j = $j+1;
	    }
	    
	}
    }

    return (-1,0,0,0,0,0) if ($max_score < 25.0);

    # TRACEBACK!
    my $start_i = $max_i;
    my $start_j = $max_j;

    my $penult_i = $max_i;
    my $penult_j = $max_j;

    my $ali_len = 0;
    
    while ($Matrix[$start_i][$start_j] > 0) {

	$penult_i = $start_i;
	$penult_j = $start_j;
	
	my $cell_score = $Matrix[$start_i][$start_j];
	
	my $match_score = GetB62Score($Seq1[$start_i-1],$Seq2[$start_j-1]);

	if ($cell_score == $Matrix[$start_i-1][$start_j-1] + $match_score) {
	    
	    $start_i--;
	    $start_j--;

	} elsif ($cell_score == $Matrix[$start_i-1][$start_j] + $b62_gap) {

	    $start_i--;
	    
	} else {

	    $start_j--;
	    
	}
	
	$ali_len++;

    }

    $start_i = $penult_i;
    $start_j = $penult_j;

    my $score_density = $max_score / $ali_len;


    # FINALLY!  Note that we're returning the original max local score,
    # which may not be representative of where we've trimmed the alignment.
    # NOTE that we need to reduce by 1 because our matrix corresponds to
    #   1-indexed sequences.
    return($score_density,$max_score,$start_i-1,$max_i-1,$start_j-1,$max_j-1);

}






###############################################################
#
#  Function:  GetB62Score
#
sub GetB62Score
{
    my $seqstr1 = shift;
    my $seqstr2 = shift;

    # If either of our sequences involves a stop codon, we're unhappy
    if ($seqstr1 =~ /\*/ || $seqstr2 =~ /\*/) {
	return -100.0;
    }

    my @Chars1 = split(//,$seqstr1);
    my @Chars2 = split(//,$seqstr2);
    my $len1 = scalar(@Chars1);
    my $len2 = scalar(@Chars2);

    my $score = 0.0;
    my $score_mult = 1.0 / ($len1 * $len2);
    for (my $i=0; $i<$len1; $i++) {

	my $char1 = $Chars1[$i];
	next if (!$AminoIndex{$char1});
	$char1 = $AminoIndex{$char1} * 21;
	
	for (my $j=0; $j<$len2; $j++) {

	    my $char2 = $Chars2[$j];
	    next if (!$AminoIndex{$char2});
	    $char2 = $AminoIndex{$char2};

	    $score += $Blosum62[$char1+$char2] * $score_mult;

	}
    }

    return $score;
    
}






###############################################################
#
#  Function:  MultiAminoSeqAli
#
sub MultiAminoSeqAli
{
    my $seqs_1_ref = shift;
    my $seqs_2_ref = shift;

    my @Seqs1 = @{$seqs_1_ref};
    my @Seqs2 = @{$seqs_2_ref};

    my $len1 = scalar(@Seqs1);
    my $len2 = scalar(@Seqs2);

    my @Matrix;
    for (my $i=0; $i<=$len1; $i++) { $Matrix[$i][0] = $i * $b62_gap; }
    for (my $j=0; $j<=$len2; $j++) { $Matrix[0][$j] = $j * $b62_gap; }

    for (my $i=0; $i<$len1; $i++) {
	for (my $j=0; $j<$len2; $j++) {

	    my $match = GetB62Score($Seqs1[$i],$Seqs2[$j]);

	    $Matrix[$i+1][$j+1] = Max($Matrix[$i][$j] + $match,
				      Max($Matrix[$i][$j+1],$Matrix[$i+1][$j]) + $b62_gap);
	    
	}
    }

    my $gapstr1 = '-';
    while (length($gapstr1) < length($Seqs1[0])) { $gapstr1 = $gapstr1.'-'; }

    my $gapstr2 = '-';
    while (length($gapstr2) < length($Seqs2[0])) { $gapstr2 = $gapstr2.'-'; }

    # Time to back-trace!
    my @Ali;
    my $i=$len1;
    my $j=$len2;
    while ($i && $j) {

	my $match = GetB62Score($Seqs1[$i-1],$Seqs2[$j-1]);

	if ($Matrix[$i][$j] == $Matrix[$i-1][$j-1] + $match) {

	    push(@Ali,$Seqs1[$i-1].$Seqs2[$j-1]);
	    $i--;
	    $j--;

	} elsif ($Matrix[$i][$j] == $Matrix[$i-1][$j] + $b62_gap) {

	    push(@Ali,$Seqs1[$i-1].$gapstr2);
	    $i--;

	} else {

	    push(@Ali,$gapstr1.$Seqs2[$j-1]);
	    $j--;

	}

    }

    while ($i) {

	push(@Ali,$Seqs1[$i-1].$gapstr2);
	$i--;

    }

    while ($j) {

	push(@Ali,$gapstr1.$Seqs2[$j-1]);
	$j--;

    }

    # Uh-oh!  That alignment is BACKWARDS!!!
    for (my $i=0; $i<scalar(@Ali)/2; $i++) {
	my $tmp = $Ali[$i];
	$Ali[$i] = $Ali[scalar(@Ali)-1-$i];
	$Ali[scalar(@Ali)-1-$i] = $tmp;
    }

    return \@Ali;
    
}







###############################################################
#
#  Function:  RecordFrameConflict
#
sub RecordFrameConflict
{
    my $fname = shift;
    
    my $target_species = shift;
    my $chr = shift;
    my $revcomp = shift;
    my $search_start = shift;
    my $search_end = shift;
    my $nucl_seq = shift;
    my $best_frame_num = shift;
    my $frame_trans_ref = shift;
    
    my @FrameTranslations = @{$frame_trans_ref};

    my $matched_ids_ref = shift;
    my $unmatched_ids_ref = shift;
    my $unmatched_frames_ref = shift;
    my $source_species_ref = shift;
    my $source_seqs_ref = shift;

    my @MatchedSourceIDs = @{$matched_ids_ref};
    my @UnmatchedSourceIDs = @{$unmatched_ids_ref};
    my @UnmatchedFramePrefs = @{$unmatched_frames_ref};
    my @SourceSpecies = @{$source_species_ref};
    my @SourceSeqs = @{$source_seqs_ref};

    my $file_exists = 0;
    if (-e $fname) {
	$file_exists = 1;
    }

    open(my $outf,'>>',$fname) || die "\n  ERROR: Failed to open output file '$fname'\n\n";

    if ($file_exists) {
	print $outf "===========================================================\n\n\n";
    }
    
    if ($revcomp) {
	$chr = $chr.'[revcomp]';
    }

    print $outf "Target Species : $target_species\n";
    print $outf "Search Range   : $chr:$search_start..$search_end\n";
    print $outf "Nucleotides    : ";
    my @Nucls = split(//,$nucl_seq);
    for (my $i=0; $i<scalar(@Nucls); $i++) {
	print $outf "$Nucls[$i]";
	if ($i+1 < scalar(@Nucls) && ($i+1) % 60 == 0) {
	    print $outf "\n                 ";
	}
    }
    print $outf "\n\n";

    print $outf "MSA Frame ($best_frame_num)  : ";
    my @Seq = split(//,$FrameTranslations[$best_frame_num]);
    for (my $i=0; $i<scalar(@Seq); $i++) {
	print $outf "$Seq[$i]";
	if ($i+1 < scalar(@Seq) && ($i+1) % 60 == 0) {
	    print $outf "\n                 ";
	}
    }
    print $outf "\n\n";

    foreach my $source_id (@MatchedSourceIDs) {
	print $outf "                 + $SourceSpecies[$source_id]\n";
    }
    print $outf "\n";
    
    my %PrefFramesToSpecies;
    my %SpeciesToIDs;
    for (my $i=0; $i<scalar(@UnmatchedFramePrefs); $i++) {
	my $pref_frame = $UnmatchedFramePrefs[$i];
	my $source_species = $SourceSpecies[$UnmatchedSourceIDs[$i]];
	$SpeciesToIDs{$source_species} = $i+1;
	if ($PrefFramesToSpecies{$pref_frame}) {
	    $PrefFramesToSpecies{$pref_frame} = $PrefFramesToSpecies{$pref_frame}.','.$source_species;
	} else {
	    $PrefFramesToSpecies{$pref_frame} = $source_species;
	}
    }

    for (my $frame=0; $frame<3; $frame++) {

	next if ($frame == $best_frame_num);

	print $outf "    Frame  $frame   : ";
	my @Seq = split(//,$FrameTranslations[$frame]);
	for (my $i=0; $i<scalar(@Seq); $i++) {
	    print $outf "$Seq[$i]";
	    if ($i+1 < scalar(@Seq) && ($i+1) % 60 == 0) {
		print $outf "\n                 ";
	    }
	}
	print $outf "\n\n";

	if (!$PrefFramesToSpecies{$frame}) {
	    print $outf "                 - Not preferred by any source species\n\n";
	    next;
	}

	foreach my $source_species (split(/\,/,$PrefFramesToSpecies{$frame})) {
	    my $source_id = $SpeciesToIDs{$source_species}-1;
	    print $outf "                 + $source_species\n";
	    print $outf "                   $SourceSeqs[$source_id]\n\n";
	}
	
    }
    
    print $outf "\n\n";
    close($outf);
    
}






###############################################################
#
#  Function:  GenBEDOutFiles
#
sub GenBEDOutFiles
{

    # Make a list of all the genes where we had alignment outputs
    my $GenesDir = OpenDirectory($outgenesdir);
    my @GeneDirsList;
    while (my $gene = readdir($GenesDir)) {
	
	$gene =~ s/\/$//;

	next if ($gene =~ /^\./);
	next if (!(-d $outgenesdir.$gene.'/alignments/'));

	push(@GeneDirsList,$outgenesdir.$gene);

    }
    closedir($GenesDir);

    
    # Now we can run through our genes in alphabetical order!
    foreach my $gene_dirname (sort @GeneDirsList) {

	$gene_dirname =~ /\/([^\/]+)$/;
	my $gene = $1;

	my $out_alis_dirname = $gene_dirname.'/alignments/';
	my $OutAlisDir = OpenDirectory($out_alis_dirname);
	while (my $target_filename = readdir($OutAlisDir)) {

	    next if ($target_filename !~ /^(\S+)\.$gene\.out/);
	    my $target_species = $1;

	    $target_filename = $out_alis_dirname.$target_filename;

	    open(my $BEDFile,'>>',$bedfilesdir.$target_species.'.bed')
		|| die "\n  ERROR:  Failed to open .bed file for species '$target_species'\n\n";
	    my $TargetFile = OpenInputFile($target_filename);
	    while (my $line = <$TargetFile>) {

		next if ($line !~ /Target\s+\:\s+\S+\s+(\S+)\:(\d+)\.\.(\d+)\s*$/);
		my $chr = $1;
		my $start = $2;
		my $end = $3;
		my $strand = '+';

		if ($end < $start) {
		    $chr =~ s/\[revcomp\]//g;
		    my $tmp = $end;
		    $end = $start;
		    $start = $tmp;
		    $strand = '-';
		}

		$line = <$TargetFile>; # Novelty
		$line = <$TargetFile>; # Source exons

		# Currently we're only doing single exon searches
		$line =~ /\: Exon (\d+)/;
		my $exon_range = $gene.'-exon_'.$1;
		    
		my $best_pct_id = 0.0;
		$line = <$TargetFile>;
		while ($line =~ /\/ (\S+)\% alignment identity/) {
		    my $next_pct_id = (0.0 + $1) / 100.0;
		    if ($next_pct_id > $best_pct_id) {
			$best_pct_id = $next_pct_id;
		    }
		    $line = <$TargetFile>;
		}

		print $BEDFile "$chr $start $end $exon_range $best_pct_id $strand\n";
		
	    }
	    close($BEDFile);
	    
	}
	closedir($OutAlisDir);
	
    }

}






#################################################################
#
#  Function:  CollapseAndCountOverlaps
#
sub CollapseAndCountOverlaps
{
    my $range_list_ref = shift;
    my @RangeList = @{$range_list_ref};

    my $known_exon_ref = shift;
    my @KnownExon = @{$known_exon_ref};
    
    my @RangeStarts;
    my @RangeEnds;
    foreach my $range (@RangeList) {
	$range =~ /^(\d+)\.\.(\d+)$/;
	push(@RangeStarts,$1);
	push(@RangeEnds,$2);
    }
    
    my $num_ranges = scalar(@RangeList);
    
    # Because we're just identifying overlaps, we can swap things around
    # so that start < end (i.e., de-revcomp)
    if ($RangeStarts[0] > $RangeEnds[0]) {
	for (my $i=0; $i<$num_ranges; $i++) {
	    my $temp = $RangeStarts[$i];
	    $RangeStarts[$i] = $RangeEnds[$i];
	    $RangeEnds[$i] = $temp;
	}
    }
    
    my %StartsToEnds;
    my %StartsToKnownExons;
    for (my $i=0; $i<$num_ranges; $i++) {
	my $start = $RangeStarts[$i];
	my $end = $RangeEnds[$i];
	if (!$StartsToEnds{$start}
	    || ($StartsToEnds{$start} && $StartsToEnds{$start} < $end)) {
	    $StartsToEnds{$start} = $end;
	}
	if ($KnownExon[$i]) {
	    $StartsToKnownExons{$start} = 1;
	}
    }
    
    my @CollapsedStarts = sort { $a <=> $b } keys %StartsToEnds;
    my @CollapsedEnds;
    foreach my $start (@CollapsedStarts) {
	push(@CollapsedEnds,$StartsToEnds{$start});
    }

    my $num_known = 0;
    my $is_known = 0;
    $is_known = 1 if ($StartsToKnownExons{$CollapsedStarts[0]});
    my $num_exons = 1;
    my $current_end = $CollapsedEnds[0];
    for (my $i=1; $i<scalar(@CollapsedEnds); $i++) {
	if ($current_end < $CollapsedStarts[$i]) {
	    $num_exons++;
	    $num_known += $is_known;
	    $is_known = 0;
	}
	$is_known = 1 if ($StartsToKnownExons{$CollapsedStarts[$i]});
	$current_end = Max($current_end,$CollapsedEnds[$i]);
    }

    $num_known += $is_known;

    return ($num_exons,$num_known);
    
}












###############################################################
#
#  Function:  RangesOverlap
#
sub RangesOverlap
{
    my $range1 = shift;
    my $range2 = shift;

    $range1 =~ /^(\d+)\.\.(\d+)$/;
    my $r1_start = $1;
    my $r1_end   = $2;

    $range2 =~ /^(\d+)\.\.(\d+)$/;
    my $r2_start = $1;
    my $r2_end   = $2;

    my $overlap = 0;
    my $full_start = 0;
    my $full_end = 0;
    
    if ($r1_start < $r1_end) {

	# Forward strand (if we're looking at genomic sequence)
	if (($r1_start <= $r2_start && $r1_end >= $r2_start)
	    || ($r2_start <= $r1_start && $r2_end >= $r1_start)) {

	    $overlap = 1;
	    $full_start = Min($r1_start,$r2_start);
	    $full_end = Max($r1_end,$r2_end);
	    
	}

    } elsif (($r1_start >= $r2_start && $r1_end <= $r2_start)
	     || ($r2_start >= $r1_start && $r2_end <= $r1_start)) {

	# Reverse strand
	$overlap = 1;
	$full_start = Max($r1_start,$r2_start);
	$full_end = Min($r1_end,$r2_end);

    }

    return ($overlap,$full_start.'..'.$full_end);
    
}




#################################################################
#
#  Function:  IsGTFAnnotated
#
sub IsGTFAnnotated
{
    
    my $species = shift;
    my $chr = shift;
    my $start = shift;
    my $end = shift;

    my $strand = '+';
    $strand = '-' if ($start > $end);
    
    my $range = $start.'..'.$end;

    # We'll either be scanning the full GTF (small inputs), or looking
    # at the narrow range of the hit in the appropriate 'micro_gtf' file.
    my $gtf_overlap = 0;
    my $full_range; # dummy var
    if (!$micro_gtfs_dirname) {

	last if (!$SpeciesToGTF{$species});
	
	my $GTF = OpenInputFile($SpeciesToGTF{$species});
	while (my $line = <$GTF>) {

	    next if ($line !~ /^\s*(\S+)\s+\S+\s+(\S+)\s+(\d+)\s+(\d+)\s+\S+\s+(\S+)/);
	    
	    my $gtf_chr    = $1;
	    my $gtf_type   = lc($2);
	    my $gtf_start  = $3;
	    my $gtf_end    = $4;
	    my $gtf_strand = $5;
	    
	    if ($gtf_type ne 'cds' && $gtf_type ne 'exon')  { next; }
	    if ($gtf_chr ne $chr || $gtf_strand ne $strand) { next; }

	    my $gtf_range = $gtf_start.'..'.$gtf_end;
	    if ($strand eq '-') {
		$gtf_range = $gtf_end.'..'.$gtf_start;
	    }
	    
	    ($gtf_overlap,$full_range) = RangesOverlap($range,$gtf_range);
	    last if ($gtf_overlap);
	    
	}
	close($GTF);

    } else {
    
	foreach my $hash_key (CoordsToGTFHashKeys($start,$end,$chr,$strand)) {
	    
	    my $micro_gtf_fname = GTFHashKeyToFname($species,$hash_key);
	    next if (!(-e $micro_gtf_fname));
	    
	    my $MicroGTF = OpenInputFile($micro_gtf_fname);
	    while (my $line = <$MicroGTF>) {
		if ($line =~ /^(\d+\.\.\d+)/) {
		    
		    ($gtf_overlap,$full_range) = RangesOverlap($range,$1);
		    last if ($gtf_overlap);
		    
		}
	    }
	    close($MicroGTF);
	    
	    last if ($gtf_overlap);
	    
	}

    }
	
    return $gtf_overlap;
    
}







#################################################################
#
#  Function:  RecordHitsByPctID
#
sub RecordHitsByPctID
{
    
    my $genesdirname = ConfirmDirectory($outdirname.'Results-by-Gene');

    my $max_gene_len = 0;
    my $max_species_len = 0;
    my $max_ali_len = 0;
    my $max_chr_len = 0;

    # We'll gather some summary statistics to (potentially) output
    # at the very end of the script's execution
    my $total_hits = 0;
    my $total_non_gtf_hits = 0;
    my %TargetToHits;
    my %TargetToNonGTFHits;
    
    my $GenesDir = OpenDirectory($genesdirname);
    my %PctIDtoHits;
    while (my $gene = readdir($GenesDir)) {
	
	my $genealisdirname = ConfirmDirectory($genesdirname.$gene).'alignments/';
	next if (!(-d $genealisdirname));
	
	$gene =~ s/\/$//;
	
	if (length($gene) > $max_gene_len) {
	    $max_gene_len = length($gene);
	}
	
	my $AliDir = OpenDirectory($genealisdirname);
	while (my $ali = readdir($AliDir)) {
	    
	    next if ($ali !~ /^([^\.]+)\./);
	    my $target_species = $1;
	    
	    my $alifname = $genealisdirname.$ali;
	    my $alif = OpenInputFile($alifname);
	    
	    my $genome_coords;
	    my $is_novel_exon;
	    while (my $line = <$alif>) {
		
		if ($line =~ /Target \: \S+ (\S+)/) {
		    $genome_coords = $1;
		    next;
		}

		if ($line =~ /\: Novel exon/) {

		    $total_hits++;
		    if ($TargetToHits{$target_species}) { $TargetToHits{$target_species}++; }
		    else                                { $TargetToHits{$target_species}=1; }
		    
		    $total_non_gtf_hits++;
		    if ($TargetToNonGTFHits{$target_species}) { $TargetToNonGTFHits{$target_species}++; }
		    else                                      { $TargetToNonGTFHits{$target_species}=1; }
		    
		    $is_novel_exon=1;
		    next;

		}

		if ($line =~ /\: Overlaps/) {

		    $total_hits++;
		    if ($TargetToHits{$target_species}) { $TargetToHits{$target_species}++; }
		    else                                { $TargetToHits{$target_species}=1; }
		    
		    $is_novel_exon=0;
		    next;

		}
		
		if ($line =~ /\: (\S+) \/ aminos (\d+)\.\.(\d+) \S+ \/ (\S+)\% ali/) {
		    
		    my $source_species = $1;
		    my $ali_len = $3 - $2 + 1;
		    my $pct_id = $4;

		    my $hash_val = $gene.':'.$source_species.'>'.$target_species.'('.$genome_coords.'):'.$ali_len.'&'.$is_novel_exon;
		    
		    if ($PctIDtoHits{$pct_id}) {
			$PctIDtoHits{$pct_id} = $PctIDtoHits{$pct_id}.'|'.$hash_val;
		    } else {
			$PctIDtoHits{$pct_id} = $hash_val;
		    }
		    
		    if (length($source_species) > $max_species_len) {
			$max_species_len = length($source_species);
		    }
		    if (length($target_species) > $max_species_len) {
			$max_species_len = length($target_species);
		    }
		    if (length($genome_coords)+3 > $max_chr_len) {
			$max_chr_len = length($genome_coords)+3;
		    }
		    if (length($ali_len) > $max_ali_len) {
			$max_ali_len = length($ali_len);
		    }
		    
		}
		
	    }
	    close($alif);
	    
	}
	closedir($AliDir);
	
    }
    closedir($GenesDir);
    

    # At long last, we have all the data we need!  Now to just scream
    # about it!
    my $OutFile = OpenOutputFile($outdirname.'Hits-by-Pct-ID.out');

    foreach my $pct_id (sort {$b <=> $a} keys %PctIDtoHits) {
	
	my %HitsByLen;
	foreach my $hit (split(/\|/,$PctIDtoHits{$pct_id})) {
	    $hit =~ /\:(\d+)\&/;
	    my $len = $1;
	    if ($HitsByLen{$len}) {
		$HitsByLen{$len} = $HitsByLen{$len}.'|'.$hit;
	    } else {
		$HitsByLen{$len} = $hit;
	    }
	}
	
	my @OrderedHits;
	foreach my $len (sort {$b <=> $a} keys %HitsByLen) {
	    foreach my $hit (split(/\|/,$HitsByLen{$len})) {
		
		$hit =~ /^([^\&]+)\&(\d)$/;
		my $hit_str  = $1;
		my $is_novel = $2;

		$hit_str =~ /^([^\:]+)\:(\S+)\>(\S+)(\(\S+\))\:(\d+)/;
		my $gene = $1;
		my $source_species = $2;
		my $target_species = $3;
		my $target_chr = $4;
		my $ali_len = $5;
		
		while (length($gene) < $max_gene_len) {
		    $gene = $gene.' ';
		}
		while (length($source_species) < $max_species_len) {
		    $source_species = $source_species.' ';
		}
		while (length($target_species) < $max_species_len) {
		    $target_species = $target_species.' ';
		}
		while (length($target_chr) < $max_chr_len) {
		    $target_chr = $target_chr.' ';
		}
		while (length($ali_len) < $max_ali_len) {
		    $ali_len = ' '.$ali_len;
		}
		
		my $formatted_str;
		if ($is_novel) { $formatted_str = '[ Novel ] '; }
		else           { $formatted_str = '[  GTF  ] '; }
		$formatted_str = $formatted_str."$gene $source_species -> $target_species ";
		$formatted_str = $formatted_str."$target_chr $ali_len aminos";
		
		push(@OrderedHits,$formatted_str);
		
	    }
	}
	
	$pct_id = $pct_id.'%';
	while (length($pct_id) < 6) {
	    $pct_id = ' '.$pct_id;
	}
	
	for (my $i=0; $i<scalar(@OrderedHits); $i++) {
	    print $OutFile "$pct_id :$OrderedHits[$i]\n";
	}
	
    }

    
    # Don't go breakin' my heart, now  :'(
    if ($total_hits == 0) {
	return "\n  No novel coding regions uncovered\n\n";
    }


    # We have at least *some* hits to report!
    my $results_overview_str = "  Total number of exons uncovered by Diviner: $total_hits\n";
    foreach my $target_species (sort keys %TargetToHits) {
	$results_overview_str = $results_overview_str."    + $target_species: $TargetToHits{$target_species}\n";
    }
    $results_overview_str = $results_overview_str."\n";

    
    # Did we have any extra-novel (i.e., non-GTF overlapping) hits?
    if ($total_non_gtf_hits == 0) {

	$results_overview_str = $results_overview_str."  All uncovered exons overlap with GTF-annotated coding regions\n";
	
    } else {

	$results_overview_str = $results_overview_str."  Exons without overlapping GTF annotations:  $total_non_gtf_hits\n";
	foreach my $target_species (sort keys %TargetToNonGTFHits) {
	    $results_overview_str = $results_overview_str."    + $target_species: $TargetToNonGTFHits{$target_species}\n";
	}

    }

    # Told 'ya we'd return this string!
    return $results_overview_str;

}






# EOF
