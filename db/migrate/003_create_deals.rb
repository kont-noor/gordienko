class CreateDeals < ActiveRecord::Migration
  def self.up
    create_table :deals do |t|
      t.integer :deal_id
      t.string :market
      t.string :name
      t.string :category
      t.string :subcategory
	  t.decimal :price, :precision => 10, :scale => 2
	  t.boolean :for_mom, :default => false
	  t.boolean :for_girl, :default => false
	  t.boolean :for_guy, :default => false
	  t.text :data
      t.timestamps
    end
  end

  def self.down
    drop_table :deals
  end
end
