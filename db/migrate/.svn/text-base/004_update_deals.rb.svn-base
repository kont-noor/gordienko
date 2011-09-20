class UpdateDeals < ActiveRecord::Migration
  def self.up
	add_column :deals, :buy_url, :string
	remove_column :deals, :for_mom
	remove_column :deals, :for_guy
	remove_column :deals, :for_girl
  end

  def self.down
	remove_column :deals, :buy_url
	add_column :deals, :for_mom, :boolean, :default => false
	add_column :deals, :for_guy, :boolean, :default => false
	add_column :deals, :for_girl, :boolean, :default => false
  end
end
