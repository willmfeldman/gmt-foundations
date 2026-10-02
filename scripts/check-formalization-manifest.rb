#!/usr/bin/env ruby
# Validate formalization.yaml against the repository.
#
# Metadata checks (no Lean): every target names an existing lean_file that contains the
# declaration; the external challenge inventory equals challenges/*/config.json; each workspace
# is complete, on the root toolchain, trusted-only by default, with a Mathlib-only Vocabulary.lean
# and a Mathlib-only Challenge.lean (its generated-block layout is checked by
# scripts/challenge-prep.py check); config theorem names and permitted axioms agree
# with the manifest; every target's challenge theorem is listed; the pinned Comparator tool
# revisions agree with scripts/release-comparator.sh; the recorded Mathlib rev agrees with
# lakefile.toml and lake-manifest.json; and each workspace's lake-manifest.json locks exactly
# the root manifest's package revisions.
#
# Lean checks (after `lake build`): every lean_name and statement_interface resolves, and every
# target depends on exactly axioms.expected.
#
# Usage: ruby scripts/check-formalization-manifest.rb [--metadata-only]
require 'yaml'
require 'json'
require 'open3'
require 'tempfile'
require 'pathname'

ROOT = Pathname.new(__dir__).parent
LEAN_NAME = /\A[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\z/
metadata_only = ARGV == ['--metadata-only']
abort 'usage: check-formalization-manifest.rb [--metadata-only]' unless ARGV.empty? || metadata_only
Dir.chdir(ROOT)
failures = []

manifest = YAML.safe_load_file('formalization.yaml')
abort 'formalization.yaml must be a mapping' unless manifest.is_a?(Hash)
expected_axioms = manifest.fetch('axioms').fetch('expected')
abort 'axioms.expected must be a nonempty list' unless expected_axioms.is_a?(Array) && !expected_axioms.empty?
targets = manifest.fetch('targets')
abort 'targets must be a nonempty list' unless targets.is_a?(Array) && !targets.empty?
abort 'duplicate target id' unless targets.map { |t| t.fetch('id') }.uniq.length == targets.length
root_toolchain = File.read('lean-toolchain').strip
failures << 'project.lean_toolchain differs from lean-toolchain' \
  unless manifest.fetch('project').fetch('lean_toolchain') == root_toolchain

# Targets.
targets.each do |t|
  id = t.fetch('id')
  %w[title kind lean_name lean_file statement_interface challenge challenge_theorem source statement].each do |k|
    failures << "#{id}: missing #{k}" unless t[k].is_a?(String) && !t[k].strip.empty?
  end
  [t['lean_name'], t['statement_interface'], t['challenge_theorem']].compact.each do |name|
    failures << "#{id}: invalid Lean name #{name.inspect}" unless name.match?(LEAN_NAME)
  end
  file = t['lean_file'].to_s
  if !File.file?(file)
    failures << "#{id}: lean_file #{file} does not exist"
  else
    short = t['lean_name'].to_s.sub(/\AGMTFoundations\./, '')
    failures << "#{id}: #{file} does not declare #{short}" \
      unless File.read(file).match?(/^(?:@\[[^\]]*\]\s*)?(?:public |protected )?theorem #{Regexp.escape(short)}\b/)
  end
end

# External challenge inventory.
external = manifest.fetch('comparator').fetch('external_challenges')
entries = external.fetch('entries')
abort 'comparator.external_challenges.entries must be a nonempty list' unless entries.is_a?(Array) && !entries.empty?
abort 'duplicate challenge id' unless entries.map { |e| e.fetch('id') }.uniq.length == entries.length
allowed = external.fetch('permitted_axioms')
failures << 'comparator permitted_axioms differ from axioms.expected' unless allowed.sort == expected_axioms.sort
failures << 'external_challenges.toolchain differs from lean-toolchain' unless external['toolchain'] == root_toolchain

# The recorded Mathlib rev must be the one the lakefile requires and the lockfile resolves.
root_lock = JSON.parse(File.read('lake-manifest.json'))
root_revs = root_lock.fetch('packages').to_h { |pkg| [pkg.fetch('name'), pkg['rev']] }
mathlib_lock = root_lock.fetch('packages').find { |pkg| pkg.fetch('name') == 'mathlib' }
lakefile_rev = File.read('lakefile.toml')[/^\[\[require\]\]\s*\nname = "mathlib"\s*\n(?:[^\[\n]*\n)*?rev = "([^"]+)"/, 1]
[['project.mathlib', manifest.fetch('project')['mathlib']], ['external_challenges.mathlib', external['mathlib']]].each do |key, rev|
  failures << "#{key} #{rev.inspect} differs from the lakefile's Mathlib rev #{lakefile_rev.inspect}" \
    unless rev == lakefile_rev
end
failures << 'lake-manifest.json Mathlib inputRev differs from lakefile.toml' \
  unless mathlib_lock && mathlib_lock['inputRev'] == lakefile_rev

listed = entries.map { |e| e.fetch('path') }.sort
on_disk = Dir.glob('challenges/*/config.json').map { |c| File.dirname(c) }.sort
unless listed == on_disk
  failures << "challenge inventory differs from formalization.yaml: " \
              "#{(on_disk - listed).inspect} unlisted, #{(listed - on_disk).inspect} missing"
end

entries.each do |entry|
  path = entry.fetch('path')
  next unless File.directory?(path)
  %w[Vocabulary.lean Challenge.lean Solution.lean config.json lakefile.toml lake-manifest.json lean-toolchain].each do |f|
    failures << "#{path}: missing #{f}" unless File.file?(File.join(path, f))
  end
  toolchain = File.join(path, 'lean-toolchain')
  failures << "#{path}: lean-toolchain differs from the root" \
    if File.file?(toolchain) && File.read(toolchain).strip != root_toolchain
  lock = File.join(path, 'lake-manifest.json')
  if File.file?(lock)
    revs = JSON.parse(File.read(lock)).fetch('packages').reject { |pkg| pkg['type'] == 'path' }
                                     .to_h { |pkg| [pkg.fetch('name'), pkg['rev']] }
    failures << "#{path}: lake-manifest.json package revisions differ from the root manifest" \
      unless revs == root_revs
  end
  imports = lambda do |f|
    File.file?(f) ? File.read(f).scan(/^\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)/).flatten : []
  end
  mathlib_only = ->(names) { !names.empty? && names.all? { |n| n == 'Mathlib' || n.start_with?('Mathlib.') } }
  failures << "#{path}: Vocabulary.lean must import Mathlib only" \
    unless mathlib_only.call(imports.call(File.join(path, 'Vocabulary.lean')))
  failures << "#{path}: Challenge.lean must import Mathlib only" \
    unless mathlib_only.call(imports.call(File.join(path, 'Challenge.lean')))
  lakefile = File.join(path, 'lakefile.toml')
  if File.file?(lakefile)
    defaults = File.read(lakefile)[/^defaultTargets\s*=\s*\[([^\]]*)\]/, 1].to_s
    failures << "#{path}: Solution must not be a default target" if defaults.include?('Solution')
  end
  config_path = File.join(path, 'config.json')
  next unless File.file?(config_path)
  config = JSON.parse(File.read(config_path))
  failures << "#{path}: theorem_names differ from formalization.yaml" \
    unless config.fetch('theorem_names') == entry.fetch('theorem_names')
  failures << "#{path}: permitted_axioms differ from formalization.yaml" \
    unless config.fetch('permitted_axioms').sort == allowed.sort
  failures << "#{path}: unexpected challenge module" unless config.fetch('challenge_module') == 'Challenge'
  failures << "#{path}: unexpected solution module" unless config.fetch('solution_module') == 'Solution'
end

challenge_theorems = entries.flat_map { |e| e.fetch('theorem_names').map { |n| [e.fetch('path'), n] } }.sort
target_theorems = targets.map { |t| [t['challenge'], t['challenge_theorem']] }.sort
unless challenge_theorems == target_theorems
  failures << "challenge theorems differ from the targets' challenge_theorem fields: " \
              "#{(challenge_theorems - target_theorems).inspect} without a target, " \
              "#{(target_theorems - challenge_theorems).inspect} not in any config"
end

driver = File.read('scripts/release-comparator.sh')
{ 'comparator_revision' => 'COMPARATOR_REV',
  'lean4export_revision' => 'LEAN4EXPORT_REV',
  'landrun_revision' => 'LANDRUN_REV' }.each do |key, var|
  pinned = driver[/^#{var}=(\h+)$/, 1]
  failures << "#{key} #{external[key].inspect} differs from #{var} in scripts/release-comparator.sh" \
    unless pinned && external[key] == pinned
end

abort failures.join("\n") unless failures.empty?
if metadata_only
  puts "Validated #{targets.length} targets and #{entries.length} challenge workspaces (metadata only)"
  exit 0
end

# Lean: one invocation resolves every name and prints the axioms of every target.
names = targets.flat_map { |t| [t.fetch('lean_name'), t.fetch('statement_interface')] }.uniq
Tempfile.create(['manifest-check-', '.lean']) do |file|
  file.puts 'import GMTFoundations'
  names.each { |n| file.puts "#check @#{n}" }
  targets.each_with_index do |t, i|
    file.puts %Q(#eval IO.println "AXIOMS_BEGIN_#{i}")
    file.puts "#print axioms #{t.fetch('lean_name')}"
    file.puts %Q(#eval IO.println "AXIOMS_END_#{i}")
  end
  file.flush
  output, status = Open3.capture2e('lake', 'env', 'lean', file.path)
  output.force_encoding(Encoding::UTF_8)
  unless status.success?
    warn output
    abort 'Lean name resolution or axiom check failed'
  end
  targets.each_with_index do |t, i|
    name = t.fetch('lean_name')
    section = output[/AXIOMS_BEGIN_#{i}(.*?)AXIOMS_END_#{i}/m, 1]
    abort "missing #print axioms output for #{name}" unless section
    actual = if section.include?('does not depend on any axioms')
               []
             else
               block = section[/depends on axioms: \[([^\]]*)\]/, 1]
               abort "unrecognized #print axioms output for #{name}: #{section}" unless block
               block.split(',').map(&:strip).uniq
             end
    failures << "#{name}: axioms #{actual.sort.inspect}, expected #{expected_axioms.sort.inspect}" \
      unless actual.sort == expected_axioms.sort
  end
end
abort failures.join("\n") unless failures.empty?
puts "Validated #{targets.length} targets (names resolve; axioms exactly #{expected_axioms.sort.inspect}) " \
     "and #{entries.length} challenge workspaces"
