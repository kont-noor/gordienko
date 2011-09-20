require 'rubygems'
require 'activerecord'
require 'yaml'
require 'log4r'

task :default => [:migrate]

  desc "Migrate the database"
  task (:migrate) do
    rack_env = ENV['RACK_ENV'] != nil ? ENV['RACK_ENV'] : 'development'
    File.open( 'config/database.yml' ) do |yf|
      YAML.load_documents( yf ) do |ydoc|
	    #puts ENV.inspect
	    #puts ydoc['development'].inspect
        ActiveRecord::Base.logger = Log4r::Logger.new("Application Log")
	    ActiveRecord::Base.establish_connection(ydoc[rack_env])
      end
    end

    ActiveRecord::Migration.verbose = true
    ActiveRecord::Migrator.migrate("db/migrate")
  end

