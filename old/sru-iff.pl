#! /usr/bin/perl -w

use strict;
use warnings;
use Catmandu;
use Catmandu -load;
my $importer = Catmandu->importer('unicat', query => 'data');
my $fixer    = Catmandu->fixer(['marc_map("245a","title")','retain_field("title")']);
my $export   = Catmandu->exporter('CSV');

my $exporter->add_many($fixer->fix($importer));

$exporter->commit;

#use Catmandu::Importer::SRU;
 
my %attrs = (
  base => 'http://sru.swissbib.ch/sru',
  query => '(isbn=0855275103 or isbn=3110035170 or isbn=9010017362 or isbn=9014026188)',
  recordSchema => 'marcxml',
  parser => 'marcxml'
);
 
#my $importer = Catmandu::Importer::SRU->new(%attrs);

# Swissbib SRU-Service for the complete content of Swissbib: MARC XML-swissbib (less namespaces), default = 10 records
#my $server_endpoint = 'http://sru.swissbib.ch/sru/search/defaultdb?&operation=searchRetrieve'.
#'&recordSchema=info%3Asrw%2Fschema%2F1%2Fmarcxml-v1.1-light&maximumRecords=10&query=';

# needed queries
my $isbnquery   = '+dc.identifier+%3D+';
my $year_st_query = '+dc.date+%3C%3D+'; # <=
my $year_gt_query = '+dc.date+%3E%3D+'; # >=
my $anyquery    = '+dc.anywhere+%3D+';
my $sruquery;
my $record;

my $count = $importer->each(sub {
      my $schema   = $record->{recordSchema};
      print $schema;
      my $packing  = $record->{recordPacking};
      print $packing;
      my $position = $record->{recordPosition};
      print $position;
      my $data     = $record->{recordData};
      print $data;
  # ...
});

print $count;